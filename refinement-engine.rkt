#lang racket/base

(require
 (for-syntax
  racket/base
  syntax/parse)
 racket/contract
 racket/match
 "locally-nameless.rkt"
 "logical-framework.rkt")


(module hyp-pattern racket/base
  (require (for-syntax racket/base syntax/parse)
           racket/list
           racket/match
           "logical-framework.rkt")
  (provide with-hyp)

  (define (ctx-split Γ x)
    (let-values ([(Γ0 Γ1) (splitf-at Γ (λ (cell) (equal? x (car cell))))])
      (values Γ0 (ctx-ref Γ x) Γ1)))

  (define-for-syntax ctx-split-expander
    (λ (stx)
      (syntax-parse stx
        [(_ Γ0:expr (x:expr A:expr) Γ1:expr)
         (syntax/loc stx
           (app (λ (Γ) (ctx-split Γ x)) Γ0 A Γ1))])))

  (define-match-expander with-hyp
    ctx-split-expander
    ctx-split-expander))

(require 'hyp-pattern)

(module sequent racket/base
  (require (for-syntax racket/base syntax/parse)
           "locally-nameless.rkt"
           "logical-framework.rkt"
           racket/match
           racket/contract)
  (provide >> subgoals >>? >>-ty proof-state proof-state? >:)

  ;; This is a wrapper around a goal / Π type which keeps a cache of names for assumptions,
  ;; which can then be used when unpacking. The result of this is that we can have user-supplied
  ;; names in tactic scripts, even though naively that doesn't make scope-sense when thinking
  ;; of goals as Π types.
  (struct >> (names ty)
    #:omit-define-syntaxes
    #:extra-constructor-name make->>
    #:transparent
    #:property prop:bindings
    (binder
     (λ (goal frees i)
       (define names (>>-names goal))
       (define ty (>>-ty goal))
       (match-define (binder abs-ty _) (bindings-accessor ty))
       (make->> names (abs-ty ty frees i)))
     (λ (goal i new-exprs)
       (define names (>>-names goal))
       (define ty (>>-ty goal))
       (match-define (binder _ inst-ty) (bindings-accessor ty))
       (make->> names (inst-ty ty i new-exprs)))))

  ;; a telescope of goals, together with an extract (scope) binding the goals' metavariables
  (struct proof-state (tele output)
    #:transparent)

  (define (unpack-proof-state state)
    (match-define (proof-state tele output) state)
    (define xs (map (λ (g) (fresh)) tele))
    (values
     (tele->ctx xs tele)
     (instantiate output xs)))

  (define (pack-proof-state subgoals output)
    (let ([xs (map car subgoals)])
      (proof-state (ctx->tele subgoals) (abstract xs output))))

  (define-syntax (subgoals stx)
    (syntax-parse stx
      [(_ ((X:id goal:expr) ...) o:expr)
       (syntax/loc stx
         (proof-state
          (telescope (X goal) ...)
          (in-scope (X ...) o)))]))

  (define/contract (pack-goal ctx rty)
    (-> ctx? rtype? >>?)
    (let ([xs (map car ctx)])
      (make->> xs (make-Π (ctx->tele ctx) (abstract xs rty)))))

  (define/contract (unpack-goal goal)
    (-> >>? (values ctx? rtype?))
    (define xs (>>-names goal))
    (define ty (>>-ty goal))
    (values (tele->ctx xs (Π-domain ty)) (instantiate (Π-codomain ty) xs)))

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

(define/contract (eta cell)
  (-> (cons/c free-name? Π?) Λ?)
  (match cell
    [(cons x (and (app Π-domain tele) (app Π-codomain cod)))
     (let* ([xs (map (λ (sc) (fresh)) tele)]
            [ctx (tele->ctx xs tele)])
       (make-Λ
        (abstract xs (make-$ x (map eta ctx)))))]))

(define/contract ($* x Γ)
  (-> free-name? ctx? $?)
  (make-$ x (map eta Γ)))

(define/contract (Λ* Γ e)
  (-> ctx? $? Λ?)
  (define xs (map car Γ))
  (make-Λ (abstract xs e)))


(define-syntax (rule stx)
  (syntax-parse stx
    [(_ goal ((x:id subgoal) ...) extract)
     (syntax/loc stx
       (match-lambda [goal (subgoals ((x subgoal) ...) extract)]))]))

(define-syntax (define-rule stx)
  (syntax-parse stx
    [(_ head goal definition:expr ... ((x:id subgoal) ...) extract)
     (syntax/loc stx
       (define head
         (lambda (g)
           (match g
             [goal
              definition ...
              (subgoals ((x subgoal) ...) extract)]))))]))


(define tac/c
  (-> >>? proof-state?))


(define id-tac
  (λ (jdg)
    (subgoals
     ((X jdg))
     (eta (cons X (>>-ty jdg))))))

; Analogous to the THENL tactical
(define (multicut t1 . ts)
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
      [('() '()) '()]
      [((cons goal subgoals) '())
       (cons id-tac (balance-tactics subgoals '()))]
      [((cons goal subgoals) (cons tactic tactics))
       (cons tactic (balance-tactics subgoals tactics))]))

  (λ (jdg)
    (match-let ([(proof-state subgoals output) (t1 jdg)])
      (multicut/aux
       subgoals
       (balance-tactics subgoals ts)
       output
       '()
       '()))))

(define (subst es xs)
  (λ (e)
    instantiate (abstract xs e) es))

(define (map-cell f cell)
  (cons
   (car cell)
   (f (cdr cell))))

(define (map-ctx f Γ)
  (map (map-cell f) Γ))

(module+ test
  (define-signature L
    (prop () (TYPE))
    (tm () (TYPE))
    (conj ((p (Π () (prop)))
           (q (Π () (prop))))
          (prop))
    (disj ((p (Π () (prop)))
           (q (Π () (prop))))
          (prop))
    (imp ((p (Π () (prop)))
          (q (Π () (prop))))
         (prop))
    (T () (prop))
    (F () (prop))
    (nil () (tm))
    (pair ((m (Π () (tm)))
           (n (Π () (tm))))
          (tm))
    (fst ((m (Π () (tm))))
         (tm))
    (snd ((m (Π () (tm))))
         (tm))
    (inl ((m (Π () (tm)))) (tm))
    (inr ((m (Π () (tm)))) (tm))
    (split ((m (Π () (tm)))
            (l (Π ((x (Π () (tm)))) (tm)))
            (r (Π ((y (Π () (tm)))) (tm)))) ; for some reason, I can't use 'x' here
           (tm))
    
    (lam ((m (Π ((x (Π () (tm)))) (tm)))) (tm))

    (is-true ((p (Π () (prop)))) (TYPE)))

  (define-rule conj/R (>> Γ (is-true (conj p q)))
    ([X (>> Γ (is-true p))]
     [Y (>> Γ (is-true q))])
    (Λ* Γ (pair ($* X Γ) ($* Y Γ))))

  (define-rule (conj/L x x0 x1)
    (>>
     (and Γ (with-hyp Γ0 (x (Π () (is-true (conj p q)))) Γ1))
     (is-true r))
    (define Γ/pq
      (append
       Γ0
       (list (cons x0 (Π () (is-true p))) (cons x1 (Π () (is-true q))))
       (map-ctx (subst (list (pair ($ x0) ($ x1))) (list x)) Γ1)))
    ([X (>> Γ/pq (is-true (subst (list (pair ($ x0) ($ x1))) (list x) r)))])
    (Λ* Γ
        (subst
         (list (fst ($ x)) (snd ($ x)))
         (list x0 x1)
         ($* X Γ/pq))))

  (define-rule disj/R/1 (>> Γ (is-true (disj p q)))
    ([X (>> Γ (is-true p))])
    (Λ* Γ (inl ($* X Γ))))

  (define-rule disj/R/2 (>> Γ (is-true (disj p q)))
    ([X (>> Γ (is-true q))])
    (Λ* Γ (inr ($* X Γ))))

  (define-rule (disj/L x)
    (>>
     (and Γ (with-hyp Γ0 (x (Π () (is-true (disj p q)))) Γ1))
     (is-true r))
    (define (Γ/p y)
      (append
       Γ0
       (list (cons y (Π () (is-true p))))
       (map-ctx (subst (list (inl ($ y))) (list x)) Γ1)))
     (define (Γ/q y)
      (append
       Γ0
       (list (cons y (Π () (is-true q))))
       (map-ctx (subst (list (inr ($ y))) (list x)) Γ1)))
    ([L (>> (Γ/p x) (subst (list (inl ($ x))) (list x) (is-true r)))]
     [R (>> (Γ/q x) (subst (list (inr ($ x))) (list x) (is-true r)))])
    (Λ* Γ (split ($ x) (xl) ($* L (Γ/p xl)) (xr) ($* R (Γ/q xr)))))


  (define-rule (imp/R x) (>> Γ (is-true (imp p q)))
    (define (Γ/p x)
      (ctx-set Γ x (Π () (is-true p))))
    ([X (>> (Γ/p x) (is-true q))])
    (Λ* Γ (lam (x) ($* X (Γ/p x)))))

  (define-rule T/R (>> Γ (is-true (T)))
    ()
    (Λ* Γ (nil)))

  (define-rule (F/L x)
    (>>
     (and Γ (with-hyp Γ0 (x (Π () (is-true (F)))) Γ1))
     (is-true p))
    ()
    (Λ* Γ (nil)))

  (define my-script
    (multicut
     (imp/R (fresh))
     (multicut
      conj/R
      T/R
      T/R)))

  (my-script (>> '() (is-true (imp (F) (conj (T) (T)))))))
