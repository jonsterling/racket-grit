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
  (require
   (for-syntax racket/base syntax/parse)
   racket/list
   racket/match
   "logical-framework.rkt"
   "locally-nameless.rkt")
  (provide with-hyp unapply)

  (define (ctx-split Γ x)
    (let* ([p (λ (cell) (not (equal? x (car cell))))]
           [Γ0 (takef Γ p)]
           [Γ1 (cdr (dropf Γ p))])
      (values
       Γ0
       (ctx-ref Γ x)
       (λ (e)
         ctx-map
         (λ (a) (instantiate (abstract (list x) a) (list e)))
         Γ1))))

  (define-for-syntax ctx-split-expander
    (λ (stx)
      (syntax-parse stx
        [(_ Γ0:expr (x:expr A:expr) Γ1:expr)
         (syntax/loc stx
           (app (λ (Γ) (ctx-split Γ x)) Γ0 A Γ1))])))

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
                    (cons ex exs))))
            f))])))

  (define-match-expander with-hyp
    ctx-split-expander)

  (define-match-expander unapply
    unapply-hyp-expander))

(require 'hyp-pattern)

(module sequent racket/base
  (require
   (for-syntax racket/base syntax/parse)
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


(define/contract id-tac
  tac/c
  (λ (goal)
    (subgoals
     ((X goal))
     (eta (cons X (>>-ty goal))))))

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

  (λ (goal)
    (match-let ([(proof-state subgoals output) (t1 goal)])
      (multicut/aux
       subgoals
       (balance-tactics subgoals ts)
       output
       '()
       '()))))

(define (orelse t1 . ts)
  (match ts
    ['() t1]
    [(cons t ts)
     (λ (goal)
       (with-handlers
         ([exn:fail? (λ (e) ((apply orelse (cons t ts)) goal))])
         (t1 goal)))]))


(define-syntax (subst stx)
  (syntax-parse stx
    [(_ ((x:id ex:expr) ...) e:expr)
     (syntax/loc stx
       (instantiate
           (abstract (list x ...) e)
           (list ex ...)))]
    [(_ (x:id ex:expr) e:expr)
     (syntax/loc stx
       (instantiate
           (abstract (list x) e)
           (list ex)))]))


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
            (r (Π ((y (Π () (tm)))) (tm)))) ; for some reason, I can't use 'x' here. something about duplicate attributes
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
     (is-true (unapply r x)))
    (define Γ/pq
      (append
       Γ0
       (list (cons x0 (Π () (is-true p))) (cons x1 (Π () (is-true q))))
       (Γ1 (pair ($ x0) ($ x1)))))
    ([X (>> Γ/pq (is-true (r (pair ($ x0) ($ x1)))))])
    (Λ* Γ
        (subst
         ((x0 (fst ($ x)))
          (x1 (snd ($ x))))
         ($* X Γ/pq))))

  (define-rule disj/R/1 (>> Γ (is-true (disj p q)))
    ([X (>> Γ (is-true p))])
    (Λ* Γ (inl ($* X Γ))))

  (define-rule disj/R/2 (>> Γ (is-true (disj p q)))
    ([X (>> Γ (is-true q))])
    (Λ* Γ (inr ($* X Γ))))

  (define-rule (disj/L x y)
    (>>
     (and Γ (with-hyp Γ0 (x (Π () (is-true (disj p q)))) Γ1))
     (is-true (unapply r x)))
    (define (Γ/p y)
      (append
       Γ0
       (list (cons y (Π () (is-true p))))
       (Γ1 (inl ($ y)))))
    (define (Γ/q y)
      (append
       Γ0
       (list (cons y (Π () (is-true q))))
       (Γ1 (inr ($ y)))))
    ([L (>> (Γ/p y) (is-true (r (inl ($ y)))))]
     [R (>> (Γ/q y) (is-true (r (inr ($ y)))))])
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

  (let* ([x (fresh "x")]
         [y (fresh "y")]
         [goal
          (>>
           '()
           (is-true
            (imp
             (disj (T) (F))
             (conj (T) (T)))))]
         [script
          (multicut
           (imp/R x)
           (multicut
            (disj/L x y)
            (multicut
             conj/R
             T/R
             T/R)
            (F/L y)))])
    (script goal)))
