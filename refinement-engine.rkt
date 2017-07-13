#lang racket/base

(require
  (for-syntax
   racket/base
   syntax/parse
   syntax/srcloc)
  racket/contract
  racket/match
  racket/dict
  racket/stxparam
  racket/splicing
  syntax/srcloc
  "locally-nameless.rkt"
  "logical-framework.rkt")


(module+ test (require rackunit))
(provide
 unapply
 with-hyp
 splice-context
 define-rule
 probe
 multicut
 then
 orelse
 id-tac
 >> >>-ty plug* bind*
 tac/c
 subgoals var->term
 with-signature
 raise-refinement-error)

(provide >> subgoals >>? >>-ty
         proof-state proof-state? >: complete-proof? proof-extract)



(define refinement-ctx/c
  (listof
   (cons/c
    free-name?
    arity?)))

(define/contract (check-sort-refinement ctx refinement-ctx sort-refinement)
  (-> ctx? refinement-ctx/c plug? sort?)
  (define args (plug-spine sort-refinement))
  (define arity (dict-ref refinement-ctx (plug-var sort-refinement)))
  (check-spine ctx (arity-domain arity) args)
  (instantiate (arity-codomain arity) args))

; TODO: check this code and make sure it is correct
(define/contract (check-telescope-refinement ctx refinement-ctx tele)
  (-> ctx? refinement-ctx/c tele? ctx?)
  (define (aux ctx env input output)
    (match input
      ['() (reverse output)]
      [(cons sc tele)
       (define arity (check-arity-refinement ctx refinement-ctx (instantiate sc env)))
       (define x (fresh))
       (aux
        (ctx-set ctx x arity)
        (append env (list x))
        tele
        (cons (cons x arity) output))]))
  (aux ctx '()  tele '()))

(define/contract (check-arity-refinement ctx refinement-ctx arity-refinement)
  (-> ctx? refinement-ctx/c arity? arity?)
  (define dom (arity-domain arity-refinement))
  (define cod (arity-codomain arity-refinement))
  (define dom-ctx (check-telescope-refinement ctx refinement-ctx dom))
  (define xs (map car dom-ctx))
  (define tau
    (check-sort-refinement
     (append ctx dom-ctx)
     refinement-ctx
     (instantiate cod xs)))
  (make-arity (ctx->telescope dom-ctx) (abstract xs tau)))


(module hyp-pattern racket/base
  (require
    (for-syntax racket/base syntax/parse)
    racket/list
    racket/match
    racket/contract
    "logical-framework.rkt"
    "locally-nameless.rkt")
  (provide with-hyp unapply)

  (define/contract (ctx-split Γ x)
    (-> ctx? free-name? (values ctx? arity? (-> any/c ctx?)))
    (define (pred cell)
      (not (equal? x (car cell))))

    (define Γ0 (takef Γ pred))
    (define Γ1 (cdr (dropf Γ pred)))

    (values
     Γ0
     (ctx-ref Γ x)
     (λ (e)
       ctx-map
       (λ (a) (instantiate (abstract (list x) a) (list (as-term e))))
       Γ1)))

  (define-for-syntax ctx-split-expander
    (λ (stx)
      (syntax-parse stx
        [(_ Γ0:expr x:expr ((y:id B:expr) ...) A:expr Γ1:expr)
         (syntax/loc stx
           (app (λ (Γ) (ctx-split Γ x)) Γ0 (arity ((y B) ...) A) Γ1))])))

  (define-for-syntax unapply-hyp-expander
    (λ (stx)
      (syntax-parse stx
        [(_ f:expr x:expr ...)
         (syntax/loc stx
           (app
            (λ (e)
              (λ (ex . exs)
                (instantiate
                    (abstract (list x ...) e)
                  (cons (as-term ex) (map as-term exs)))))
            f))])))

  (define-match-expander with-hyp
    ctx-split-expander)

  (define-match-expander unapply
    unapply-hyp-expander))

(require 'hyp-pattern)

(define-syntax (splice-context stx)
  (syntax-parse stx
    [(_ Γ0:expr ((x:expr ty:expr) ...) Γ1:expr)
     (syntax/loc stx
       (append Γ0
               (list (cons x (as-arity ty)) ...)
               Γ1))]))

(module sequent racket/base
  (require
    (for-syntax racket/base syntax/parse)
    "locally-nameless.rkt"
    "logical-framework.rkt"
    racket/match
    racket/contract)
  (provide >> subgoals >>? >>-ty
           proof-state proof-state? >: complete-proof? proof-extract)

  ;; This is a wrapper around a goal which keeps a cache of names for assumptions,
  ;; which can then be used when unpacking. The result of this is that we can have user-supplied
  ;; names in tactic scripts, even though naively that doesn't make scope-sense when thinking
  ;; of goals as arities.
  (struct >> (names ty)
    #:omit-define-syntaxes
    #:extra-constructor-name make->>
    #:transparent
    #:property prop:bindings
    (bindings-support
     (λ (goal frees i)
       (define names (>>-names goal))
       (define ty (>>-ty goal))
       (match-define(bindings-support abs-ty _) (bindings-accessor ty))
       (make->> names (abs-ty ty frees i)))
     (λ (goal i new-exprs)
       (define names (>>-names goal))
       (define ty (>>-ty goal))
       (match-define(bindings-support _ inst-ty) (bindings-accessor ty))
       (make->> names (inst-ty ty i new-exprs)))))

  ;; a telescope of goals, together with an extract (scope) binding the goals' plugvariables
  (struct proof-state (tele output)
    #:transparent)

  (define/contract (complete-proof? st)
    (-> proof-state? boolean?)
    (zero? (scope-valence (proof-state-output st))))

  (define/contract (proof-extract st)
    (-> complete-proof? bind?)
    (instantiate (proof-state-output st) '()))

  (define/contract (unpack-proof-state state)
    (-> proof-state? (values ctx? bind?))
    (match-define (proof-state tele output) state)
    (define xs (map (λ (g) (fresh)) tele))
    (values
     (telescope->ctx xs tele)
     (instantiate output xs)))

  (define (pack-proof-state subgoals output)
    (let ([xs (map car subgoals)])
      (proof-state (ctx->telescope subgoals) (abstract xs output))))

  (define-syntax (subgoals stx)
    (syntax-parse stx
      [(_ ((X:id goal:expr) ...) o:expr)
       (syntax/loc stx
         (proof-state
          (telescope (X goal) ...)
          (in-scope (X ...) o)))]))

  (define/contract (pack-goal ctx rty)
    (-> ctx? sort? >>?)
    (let ([xs (map car ctx)])
      (make->> xs (make-arity (ctx->telescope ctx) (abstract xs rty)))))

  (define/contract (unpack-goal goal)
    (-> >>? (values ctx? sort?))
    (define xs (>>-names goal))
    (define ty (>>-ty goal))
    (values (telescope->ctx xs (arity-domain ty)) (instantiate (arity-codomain ty) xs)))

  (define-match-expander >>
    (λ (stx)
      (syntax-parse stx
        [(_ Γ rty)
         (syntax/loc stx
           (app unpack-goal Γ rty))]))
    (λ (stx)
      (syntax-parse stx
        [(_ Γ rty)
         (syntax/loc stx
           (pack-goal Γ rty))])))

  (define-match-expander >:
    (λ (stx)
      (syntax-parse stx
        [(_ Ψ o)
         (syntax/loc stx
           (app unpack-proof-state Ψ o))]))
    (λ (stx)
      (syntax-parse stx
        [(_ Ψ o)
         (syntax/loc stx
           (pack-proof-state Ψ o))]))))

(require 'sequent)


(define/contract (var->term cell)
  (-> (cons/c free-name? arity?) bind?)
  (match cell
    [(cons x (and (app arity-domain tele) (app arity-codomain cod)))
     (let* ([xs (map (λ (sc) (fresh)) tele)]
            [ctx (telescope->ctx xs tele)])
       (make-bind
        (abstract xs (make-plug x (map var->term ctx)))))]))

(define/contract (plug* x Γ)
  (-> free-name? ctx? plug?)
  (make-plug x (map var->term Γ)))

(define/contract (bind* Γ e)
  (-> ctx? any/c bind?)
  (define xs (map car Γ))
  (make-bind (abstract xs e)))


(struct exn:fail:refinement exn:fail (goal)
  #:transparent
  #:extra-constructor-name make-exn:fail:refinement)

(define (raise-refinement-error msg goal)
  (raise (exn:fail:refinement msg (current-continuation-marks) goal)))

(define ((ok-goal? lf-sig ref-sig) goal)
  (with-handlers ([exn:fail? (λ (_) #f)])
    (check-arity-refinement lf-sig ref-sig (>>-ty goal))
    #t))

(define (ok-proof-state? lf-sig ref-sig goal)
  (match-lambda
    [(proof-state subgoals output)
     (with-handlers ([exn:fail? (λ (_) #f)])
       (define ctx (check-telescope-refinement lf-sig ref-sig (map (λ (goal) (under-scope >>-ty goal)) subgoals)))
       (define arity (check-arity-refinement lf-sig ref-sig (>>-ty goal)))
       (check-term (append lf-sig ctx) (instantiate output (map car ctx)) arity)
       #t)]))

(define (ok-rule? lf-sig ref-sig)
  (match* (lf-sig ref-sig)
    [(#f #f) tac/c]
    [(_ _)
     (->i
      ((goal (ok-goal? lf-sig ref-sig)))
      (result (goal) (ok-proof-state? lf-sig ref-sig goal)))]))

(define-syntax-parameter default-signature #'#f)
(define-syntax-parameter default-refinement-signature #'#f)

(define-syntax (define-rule stx)
  (define (get-name h)
    (syntax-parse h
      [n:id #'n]
      [(h* e ...) (get-name #'h*)]))
  (syntax-parse stx
    [(_ head
        (~optional
         (~seq #:sig lf-sig ref-sig)
         #:defaults
         ([lf-sig (syntax-parameter-value #'default-signature)]
          [ref-sig (syntax-parameter-value #'default-refinement-signature)]))
        goal definition:expr ... ((x:id subgoal) ...) extract)
     (with-syntax ([rule-name (get-name #'head)])
       (syntax/loc stx
         (define head
           (contract
            (ok-rule? lf-sig ref-sig)
            (procedure-rename
             (λ (g)
               (match g
                 [(and (>> Γ J) goal)
                  definition ...
                  (subgoals ((x subgoal) ...) (bind* Γ extract))]
                 [other-goal
                  (raise-refinement-error (format "Inapplicable: ~a" other-goal) other-goal)]))
             'rule-name)
            'rule-name 'caller))))]))


(define-syntax (with-signature stx)
  (syntax-parse stx
    [(_ lf-sig refinement-sig body ...)
     #'(splicing-syntax-parameterize ([default-signature (syntax lf-sig)]
                                      [default-refinement-signature (syntax refinement-sig)])
         body
         ...)]))

(define tac/c
  (-> >>? proof-state?))

(define/contract id-tac
  tac/c
  (λ (goal)
    (subgoals
     ((X goal))
     (var->term (cons X (>>-ty goal))))))

; Analogous to the THENL tactical
(define/contract (multicut t1 . ts)
  (->* (tac/c)
       #:rest (listof tac/c)
       tac/c)
  (define (multicut/aux subgoals tactics output subgoals-out env-out)
    (match* (subgoals tactics)
      [('() _)
       (>: subgoals-out (instantiate output env-out))]
      [((cons goal subgoals) (cons tactic tactics))
       (match-let ([(>: subgoals1 output1) (tactic (instantiate goal env-out))])
         (multicut/aux
          subgoals
          tactics
          output
          (append subgoals-out subgoals1)
          (append env-out (list output1))))]
      [(_ _) (error "Subgoals and tactics must be of same length") ]))

  (define (balance-tactics subgoals tactics)
    (match* (subgoals tactics)
      [('() _) '()]
      [((cons goal subgoals) '())
       (cons id-tac (balance-tactics subgoals '()))]
      [((cons goal subgoals) (cons tactic tactics))
       (cons tactic (balance-tactics subgoals tactics))]))

  (λ (goal)
    (match-let ([(proof-state subgoals output) (t1 goal)])
      (multicut/aux
       subgoals
       (balance-tactics subgoals ts)
       output
       '()
       '()))))

(define/contract (then . ts)
  (->* ()
       #:rest (listof tac/c)
       tac/c)
  (match ts
    ['() id-tac]
    [(list t) t]
    [(cons t1 ts)
     (define (then/aux subgoals output subgoals-out env-out)
       (match subgoals
         ['()
          (>: subgoals-out (instantiate output env-out))]
         [(cons goal subgoals)
          (match-let ([(>: subgoals1 output1)
                       ((apply then ts) (instantiate goal env-out))])
            (then/aux
             subgoals
             output
             (append subgoals-out subgoals1)
             (append env-out (list output1))))]))
     (λ (goal)
       (match-let ([(proof-state subgoals output) (t1 goal)])
         (then/aux
          subgoals
          output
          '()
          '())))]))

(define (orelse t1 . ts)
  (match ts
    ['() t1]
    [(cons t ts)
     (λ (goal)
       (with-handlers ([exn:fail:refinement?
                        (λ (e)
                          ((apply orelse (cons t ts)) goal))])
         (t1 goal)))]))


(define/contract ((probe-at loc) goal)
  (-> source-location? tac/c)
  (printf "~a: ~a" (source-location->string loc) goal)
  (subgoals
   ([X goal])
   (var->term `(,X . ,(>>-ty goal)))))

(define-syntax (probe stx)
  (syntax-parse stx
    #:literals (probe)
    [probe
     (with-syntax
         ([source (source-location-source stx)]
          [line (source-location-line stx)]
          [col (source-location-column stx)]
          [pos (source-location-position stx)]
          [span (source-location-span stx)])
       (syntax/loc stx
         (probe-at (make-srcloc 'source 'line 'col 'pos 'span))))]))

