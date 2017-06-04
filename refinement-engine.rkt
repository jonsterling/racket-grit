#lang racket/base

(require
 (for-syntax
  racket/base
  racket/list
  syntax/parse
  racket/syntax
  (for-syntax racket/base))
 racket/contract
 racket/fixnum
 racket/function
 racket/list
 racket/match
 racket/provide-syntax
 racket/string
 racket/dict
 "locally-nameless.rkt"
 "logical-framework.rkt")


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

(define-syntax (subgoals stx)
  (syntax-parse stx
    [(_ ((X:id goal:expr) ...) o:expr)
     (syntax/loc stx
       (proof-state
        (telescope (X goal) ...)
        (in-scope (X ...) o)))]))


(define (pack-goal ctx rty)
  (let ([xs (map car ctx)])
    (make->> xs (make-Π (ctx->tele ctx) (abstract xs rty)))))

(define (unpack-goal gl)
  (define xs (>>-names gl))
  (define ty (>>-ty gl))
  (cons (tele->ctx xs (Π-domain ty)) (instantiate (Π-codomain ty) xs)))

(define-match-expander >>
  (λ (stx)
    (syntax-parse stx
      [(_ Γ rty)
       (syntax/loc stx
         (app unpack-goal (cons Γ rty)))]))
  (λ (stx)
    (syntax-parse stx
      [(_ Γ rty)
       (syntax/loc stx
         (pack-goal Γ rty))])))


(define (eta cell)
  (match cell
    [(cons x (and (app Π-domain tele) (app Π-codomain cod)))
     (let* ([xs (map (λ (sc) (fresh)) tele)]
            [ctx (tele->ctx xs tele)])
       (make-Λ
        (abstract xs (make-$ x (map eta ctx)))))]))

(define ($$ x Γ)
  (make-$ x (map eta Γ)))




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
    (inl ((m (Π () (tm)))) (tm))
    (inr ((m (Π () (tm)))) (tm))
    (lam ((m (Π ((x (Π () (tm)))) (tm)))) (tm))
    (is-true ((p (Π () (prop)))) (TYPE)))

  ;; Here are some examples of dependent refinement rules!
  ;; I haven't actually implemented the refinement machine, which would allow you to
  ;; compose these.

  (define (conj-i goal)
    (match goal
      [(>> Γ (is-true (conj p q)))
       (subgoals
        ((X (>> Γ (is-true p)))
         (Y (>> Γ (is-true q))))
        (pair ($$ X Γ) ($$ Y Γ)))]))

  (define (disj-i-1 goal)
    (match goal
      [(>> Γ (is-true (disj p q)))
       (subgoals
        ((X (>> Γ (is-true p))))
        (inl ($$ X Γ)))]))

  (define (disj-i-2 goal)
    (match goal
      [(>> Γ (is-true (disj p q)))
       (subgoals
        ((X (>> Γ (is-true q))))
        (inr ($$ X Γ)))]))

  (define ((imp-i x) goal)
    (match goal
      [(>> Γ (is-true (imp p q)))
       (let ([Γ/p (λ (x) (ctx-set Γ x (Π () (is-true p))))])
         (subgoals
          ((X (>> (Γ/p x) (is-true q))))
          (lam (x) ($$ X (Γ/p x)))))]))

  (conj-i (>> '() (is-true (conj (T) (F)))))
  ((imp-i (fresh)) (>> '() (is-true (imp (F) (T))))))
