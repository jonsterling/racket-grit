#lang racket

(require "locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt")
(require (for-syntax syntax/parse) syntax/srcloc)

(module+ test (require rackunit))

;;; Commentary:
;; This is the disk format of interactively-constructed proofs, as
;; well as an independent checker for them.
;;
;; The basic architecture will be:
;;
;;  * No higher-order data is stored. Proof trees include strings that
;;    are eval'd WRT a Racket namespace to construct both the bits of
;;    LF and the tactics. This lets us use a very simple
;;    human-readable serializer/deserializer.
;;
;;  * The proof checker takes serialized proof trees as input and
;;    emits a list of feedback. This is enough to be the basis for a
;;    somewhat primitive Emacs mode for interactively editing the dump
;;    files, as well as Travis for saved proofs.
;;
;;  * As in Nuprl, a proof consists of a goal followed by a tree of
;;    refinements. The refinement tree nodes are labeled by tactic
;;    scripts that produce the obligations solved by their subtrees.
;;    Unlike Nuprl, multiple proofs can be chained in a module.  We
;;    call nodes on which refinement has not yet been attempted
;;    "sheds", following Epigram, but they're basically just Nuprl's
;;    unrefiend nodes.
;;
;;  * One mistake should not be fatal to a whole proof, merely to the
;;    subtree underneath it.
;;
;;  * We talked about having separate presentation tactics and
;;    annotating subgoals with whether they are boring, but on further
;;    reflection, I think we should just extend a proof state so that
;;    the subgoals can have arbitrary metadata attached and then use
;;    that for the prover (like Nuprl WF goals).

;; Proofs output feedback
(struct goal-feedback (loc goal solved?) #:transparent)
(struct mistake-feedback (loc message) #:transparent)
(struct extract-feedback (loc goal) #:transparent)


(define (feedback? x)
  (or (goal-feedback? x)
      (mistake-feedback? x)
      (extract-feedback? x)))

;; A complete module development
(struct module-node (defs) #:transparent)
;; A top-level definition
(struct def-node (name goal body loc goal-loc) #:transparent)
;; A refined node in the proof. The text used to refine it is stored as a string, but it
;; will be subject to eval.
(struct by-node (text subs loc) #:transparent)
;; A shed node that records incomplete input
(struct shed-node (text loc) #:transparent)

(define current-proof-namespace
  (make-parameter (current-namespace)))

(define/contract (interpret-mod m)
  (-> module-node? (listof feedback?))
  (match m
    [(module-node defs)
     (interpret-defs '() defs)]))

(struct lemma (name prop extract))

(define/contract (interpret-defs Δ ds)
  (-> (listof lemma?) (listof def-node?) (listof feedback?))
  (match ds
    ['() '()]
    [(cons one-def more-defs)
     (with-handlers ([exn:srclocs?
                      (λ (e)
                        (define locs ((exn:srclocs-accessor e) e))
                        (if (null? locs)
                            (raise e)
                            (for/list ([l locs])
                              (mistake-feedback l (exn-message e)))))])
       (let-values ([(feedback lem) (interpret-def Δ one-def)])
         (append feedback (interpret-defs (if lem (cons lem Δ) Δ) more-defs))))]))


(struct exn:fail:proof exn (loc) #:transparent
  #:property prop:exn:srclocs
  (lambda (e)
    (list (exn:fail:proof-loc e))))

(define (proof-error message loc)
  (raise (exn:fail:proof message (current-continuation-marks) loc)))

(define/contract (interpret-def Δ d)
  (-> (listof lemma?) def-node? (values (listof feedback?) (or/c #f lemma?)))
  (match-let ([(def-node name goal body loc goal-loc) d])
    (let ([goal-val
           (with-handlers ([exn:fail? (λ (e) (proof-error (exn-message e) goal-loc))])
             (with-input-from-string goal
               (thunk (eval (read) (current-proof-namespace)))))])
      (if (not (eval `(>>? ,goal-val) (current-proof-namespace)))
          (proof-error (format "Not a goal: ~a" goal-val) goal-loc)
          (let-values ([(feedback ext) (interpret-step Δ goal-val body)])
            (values feedback
                    (if ext (lemma name goal ext) #f)))))))

(define/contract (interpret-step Δ goal s)
  (-> (listof lemma?)
      >>?
      (or/c by-node? shed-node?)
      (values (listof feedback?)
              (or/c #f bind?)))
  (cond
    [(by-node? s) (interpret-by Δ goal s)]
    [(shed-node? s) (values (list (goal-feedback (shed-node-loc s) goal #f)) #f)]
    [else (error "Invalid node")]))

(define/contract (interpret-by Δ goal b)
  (-> (listof lemma?)
      >>?
      by-node?
      (values (listof feedback?)
              (or/c #f bind?)))
  (match-let ([(by-node text sub-proofs loc) b])
    (with-handlers ([exn:fail:proof? (λ (e) (raise e))]
                    [exn:fail? (λ (e) (proof-error (exn-message e) loc))])
      (define tac-val
        (with-input-from-string text
          (thunk (eval (read) (current-proof-namespace)))))
      (match (tac-val goal)
        [(proof-state subgoals ext)
         (let loop ([feedback '()]
                    [gs subgoals]
                    [ps sub-proofs]
                    [extracts '()])
           (match* (gs ps)
             [('() '())
              (values (cons (goal-feedback loc goal #t) ;; todo check for solved
                            feedback)
                      (instantiate ext (reverse extracts)))]
             [((cons this-subgoal more-subgoals)
               (cons this-proof more-proofs))
              (define-values (this-feedback this-evidence)
                (interpret-step Δ
                                (instantiate this-subgoal (reverse extracts))
                                this-proof))
              (loop (append feedback this-feedback)
                    more-subgoals
                    more-proofs
                    (if this-evidence
                        (cons this-evidence extracts)
                        (cons (fresh) extracts)))]
             [(_ _)
              (proof-error
               (format "Refinement has ~s subgoals, but ~s scripts were provided"
                       (length subgoals) (length sub-proofs))
               loc)]))]
        [non-refinement
         (proof-error (format "Not a refinement: ~s" non-refinement) loc)]))))


;; A presentation goal is a proof goal that is either boring (to be
;; solved by automation) or a genuine problem (to be solved by human
;; refinement)
(struct presentation-goal (goal)
  #:transparent
  #:property prop:bindings
  (bindings-support
   (λ (pg frees i)
     (match-define (presentation-goal g) pg)
     (match-define (bindings-support abs _) (bindings-accessor g))
     ((if (problem? pg) problem boring)
      (abs g frees i)))
   (λ (pg i new-exprs)
     (match-define (presentation-goal g) pg)
     (match-define (bindings-support _ inst) (bindings-accessor g))
     ((if (problem? pg) problem boring)
      (inst g i new-exprs)))))
(struct problem presentation-goal () #:transparent)
(struct boring presentation-goal () #:transparent)


(struct exn:fail:read-gritty exn:fail ())

(define gritty-step/c
  (recursive-contract
   (or/c (struct/c by-node string? (listof gritty-step/c) source-location?)
         (struct/c shed-node string? source-location?))
   #:chaperone))
(define gritty-def/c (struct/c def-node string? string? gritty-step/c source-location? source-location?))
(define gritty-module/c (struct/c module-node (listof gritty-def/c)))


;; Deserialize a written Gritty file
(define/contract (read-gritty-file filename)
  (-> path-string? gritty-module/c)
  (with-input-from-file filename
    (thunk
     (port-count-lines! (current-input-port))
     (define stxs
       (for/list ([stx (in-producer (thunk (read-syntax filename)) eof-object?)])
         stx))
     (stx->mod stxs))
    #:mode 'text))

(define/contract (stx->mod stxs)
  (-> (listof syntax?) gritty-module/c)
  (module-node
   (for/list ([stx stxs])
     (stx->def stx))))

(define/contract (stx->def stx)
  (-> syntax? gritty-def/c)
  (match (syntax-e stx)
    [(list (app syntax->datum 'def) (app syntax->datum name) (and goal-loc (app syntax->datum goal)) step)
     (if (and (string? name) (string? goal))
         (def-node name goal (stx->step step) stx goal-loc)
         (raise (exn:fail:read-gritty (format "Name and goal must be strings, but are: ~a and ~a"
                                              name goal)
                                      (current-continuation-marks))))]
    [_ (raise (exn:fail:read-gritty (format "Bad def: ~a" (syntax->datum stx))
                                    (current-continuation-marks)))]))

(define/contract (stx->step stx)
  (-> syntax? gritty-step/c)
  (match (syntax-e stx)
    [(list (app syntax->datum 'shed) (app syntax->datum (? string? input)))
     (shed-node input stx)]
    [(list (app syntax->datum 'by)
           (app syntax->datum (? string? tactic))
           steps ...)
     (by-node tactic
              (for/list ([s steps ])
                (stx->step s))
              stx)]
    [_ (raise (exn:fail:read-gritty (format "Bad step: ~a" (syntax->datum stx)) (current-continuation-marks)))]))

;; Serialize a Gritty file
(define/contract (write-gritty-file mod filename #:exists (exists-flag 'error))
  (->* (gritty-module/c path-string?)
       (#:exists (or/c 'error 'append 'update 'can-update
                       'replace 'truncate
                       'must-truncate 'truncate/replace))
       void?)
  (define port (open-output-file filename #:mode 'text #:exists exists-flag))
  (for ([d (mod->sexpr mod)])
    (pretty-print d port 1))
  (close-output-port port))


(define step-sexpr/c
  (flat-rec-contract step-sexpr/c
                     (cons/c 'by (cons/c string? (listof step-sexpr/c)))
                     (list/c 'shed string?)))
(define def-sexpr/c
  (list/c 'def string? string?
          step-sexpr/c))

(define/contract (mod->sexpr mod)
  (-> gritty-module/c (listof def-sexpr/c))
  (for/list ([d (module-node-defs mod)])
    (def->sexpr d)))

(define/contract (def->sexpr def)
  (-> gritty-def/c def-sexpr/c)
  (match-define (def-node name goal step _ _) def)
  `(def ,name ,goal ,(step->sexpr step)))

(define/contract (step->sexpr step)
  (-> gritty-step/c step-sexpr/c)
  (match step
    [(shed-node text _) `(shed ,text)]
    [(by-node tactic subs _) `(by ,tactic . ,(map step->sexpr subs))]))


(define (erase-srclocs v)
  (match v
    [(module-node xs) (module-node (map erase-srclocs xs))]
    [(def-node name goal step _ _)
     (def-node name goal (erase-srclocs step) #f #f)]
    [(by-node tactic steps _)
     (by-node tactic (map erase-srclocs steps) #f)]
    [(shed-node text _)
     (shed-node text #f)]))

(define (same-proof? v1 v2)
  (equal? (erase-srclocs v1) (erase-srclocs v2)))

(define-syntax (with-logic-module stx)
  (syntax-parse stx
    [(_ logic-module body ...)
     (syntax/loc stx
       ;; This is the magic incantation to create a namespace using already-loaded modules
       (let ([ns (make-base-namespace)])
         ;; Re-use the currently-loaded versions of these modules, to avoid generativity getting
         ;; in the way of struct types etc
         (for ([mod '("locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt")])
           (namespace-attach-module (current-namespace) mod ns))
         (parameterize ([current-namespace ns])
           (for ([mod '("locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt")])
             (namespace-require mod))
           ;; Finally load the user's logic module
           (namespace-require logic-module))
         (parameterize ([current-proof-namespace ns])
           body ...)))]))

(define (gritty-check logic proof)
  (with-logic-module logic
    (define ast (read-gritty-file proof))
    (let ([feedback (interpret-mod ast)])
      (for ([f feedback])
        (match f
          [(goal-feedback loc g solved?)
           (printf "~a: ~a Goal\n" (source-location->string loc) (if solved? "Solved" "Unsolved") )
           (pretty-print g)
           (printf "\n")]
          [(mistake-feedback loc msg)
           (printf "~a: Error:\n~s\n\n" (source-location->string loc) msg)]
          [(extract-feedback loc e)
           (printf "~a: Extract:\n~s\n\n" (source-location->string loc) e)])))))

(module+ main
  (command-line
   #:program "gritty-check"
   #:args (logic proof)
   (gritty-check logic proof)))


(module+ test
  (with-logic-module "refiner-demo.rkt"
    (define-simple-check (check-serialization p)
      (define tmp (make-temporary-file "grittytest~a"))
      (write-gritty-file p tmp #:exists 'replace)
      (define p2 (read-gritty-file tmp))
      (same-proof? p p2))

    (define-simple-check (check-goal-feedback? x)
      (goal-feedback? x))

    (define-simple-check (check-mistake-feedback? x)
      (mistake-feedback? x))

    (define test-gritty-proof-1
      (module-node
       (list
        (def-node "prf"
          "(>> '() (is-true (conj (disj (T) (F)) (conj (T) (T)))))"
          (shed-node "stuff" #'here)
          #'here1
          #'here2))))

    (check-serialization test-gritty-proof-1)

    (define out-1 (interpret-mod test-gritty-proof-1))
    (check-equal? (length out-1) 1)
    (check-goal-feedback? (car out-1))

    (define test-gritty-proof-2
      (module-node
       (list
        (def-node "prf"
          "(>> '() (is-true (conj (disj (T) (F)) (conj (T) (T)))))"
          (by-node "conj/R"
                   (list
                    (shed-node "stuff" #'here)
                    (shed-node "more stuff" #'here))
                   #'here)
          #'here1
          #'here2))))

    (check-serialization test-gritty-proof-2)

    (define out-2 (interpret-mod test-gritty-proof-2))
    (check-equal? (length out-2) 3)
    (check-goal-feedback? (car out-2))
    (check-goal-feedback? (cadr out-2))
    (check-goal-feedback? (caddr out-2))

    (define test-gritty-proof-3
      (module-node
       (list
        (def-node "prf"
          "(>> '() (is-true (conj (disj (T) (F)) (conj (T) (T)))))"
          (by-node "conj/R"
                   (list
                    (by-node "(orelse (then disj/R/1 T/R) (then disj/R/2 T/R))"
                             '()
                             #'here)
                    (shed-node "more stuff" #'here))
                   #'here)
          #'here1
          #'here2))))

    (check-serialization test-gritty-proof-3)

    (define out-3 (interpret-mod test-gritty-proof-3))
    (check-equal? (length out-3) 3)
    (check-goal-feedback? (car out-3))
    (check-goal-feedback? (cadr out-3))
    (check-goal-feedback? (caddr out-3))

    (define test-gritty-proof-4
      (module-node
       (list (def-node "oops" "42" (shed-node "foo" #'here3) #'here1 #'here2))))
    (check-serialization test-gritty-proof-4)
    (define out-4 (interpret-mod test-gritty-proof-4))

    (check-equal? (length out-4) 1)
    (check-mistake-feedback? (car out-4))

    (define test-gritty-proof-5
      (module-node
       (list (def-node "easy" "(>> '() (is-true (T)))"
               (by-node "conj/R"
                        '()
                        #'here3) #'here1 #'here2))))
    (check-serialization test-gritty-proof-5)
    (define out-5 (interpret-mod test-gritty-proof-5))

    (check-equal? (length out-5) 1)
    (check-mistake-feedback? (car out-5)))

  (check-not-false
   (regexp-match #rx"Solved Goal"
                 (with-output-to-string (thunk (gritty-check "refiner-demo.rkt" "test.grit"))))))
