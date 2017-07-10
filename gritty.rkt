#lang racket

(require "locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt")

(module+ test (require rackunit))

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
  (match-define (def-node name goal body loc goal-loc) d)
  (let ([goal-val
         (with-handlers ([exn:fail? (λ (e) (proof-error (exn-message e) goal-loc))])
           (with-input-from-string goal
             (thunk (eval (read) (current-proof-namespace)))))])
    (if (not (>>? goal-val))
        (proof-error "Not a goal" goal-loc)
        (let-values ([(feedback ext) (interpret-step Δ goal-val body)])
          (values feedback
                  (if ext (lemma name goal ext) #f))))))

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
  (match-define (by-node text sub-proofs loc) b)
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
         (proof-error (format "Not a refinement: ~s" non-refinement) loc)])))




(module goals racket/base
  (require racket/match "locally-nameless.rkt")
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
  (provide (struct-out problem) (struct-out boring) presentation-goal?))
(require 'goals)

(define/contract (mark-problem goal)
  tac/c
  (subgoals
   ((X (problem goal)))
   (eta (cons X (>>-ty goal)))))

(define/contract (mark-boring goal)
  tac/c
  (subgoals
   ((X (boring goal)))
   (eta (cons X (>>-ty goal)))))

(define/contract (tactic->presentation-tactic t)
  (-> tac/c tac/c)
  (then t mark-problem))



(module+ test
  (require "refiner-demo.rkt")
  (current-proof-namespace (namespace-anchor->namespace demo-anchor))

  (define test-proof-1
    (module-node
     (list
      (def-node "prf"
        "(>> '() (is-true (conj (disj (T) (F)) (conj (T) (T)))))"
        (shed-node "stuff" #'here)
        #'here1
        #'here2))))

  (define out-1 (interpret-mod test-proof-1))
  (check-equal? (length out-1) 1)
  (check-true (goal-feedback? (car out-1)))

  (define test-proof-2
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
  (define out-2 (interpret-mod test-proof-2))
  (check-equal? (length out-2) 3)
  (check-true (andmap goal-feedback? out-2))

  (define test-proof-3
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

  (define out-3 (interpret-mod test-proof-3))
  (check-equal? (length out-3) 3)
  (check-true (andmap goal-feedback? out-3)))
