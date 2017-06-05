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


(define (ctx-split Γ x)
  (let-values ([(Γ0 Γ1) (splitf-at Γ (λ (cell) (equal? x (car cell))))])
    (list Γ0 (ctx-ref Γ x) Γ1)))

(define-for-syntax ctx-split-expander
  (λ (stx)
    (syntax-parse stx
      [(_ Γ0:expr (x:expr A:expr) Γ1:expr)
       (syntax/loc stx
         (app (λ (Γ) (ctx-split Γ x)) (list Γ0 Α Γ1)))])))

(define-match-expander with-hyp
  ctx-split-expander
  ctx-split-expander)


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


(define/contract
  (pack-goal ctx rty)
  (-> ctx? rtype? >>?)
  (let ([xs (map car ctx)])
    (make->> xs (make-Π (ctx->tele ctx) (abstract xs rty)))))

(define/contract
  (unpack-goal goal)
  (-> >>? (cons/c ctx? rtype?))
  (define xs (>>-names goal))
  (define ty (>>-ty goal))
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


(define/contract
  (eta cell)
  (-> (cons/c free-name? Π?) Λ?)
  (match cell
    [(cons x (and (app Π-domain tele) (app Π-codomain cod)))
     (let* ([xs (map (λ (sc) (fresh)) tele)]
            [ctx (tele->ctx xs tele)])
       (make-Λ
        (abstract xs (make-$ x (map eta ctx)))))]))

(define/contract
  ($$ x Γ)
  (-> free-name? ctx? $?)
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
    (fst ((m (Π () (tm))))
         (tm))
    (snd ((m (Π () (tm))))
         (tm))
    (inl ((m (Π () (tm)))) (tm))
    (inr ((m (Π () (tm)))) (tm))
    (lam ((m (Π ((x (Π () (tm)))) (tm)))) (tm))

    (is-true ((p (Π () (prop)))) (TYPE)))

  ;; Here are some examples of dependent refinement rules!
  ;; I haven't actually implemented the refinement machine, which would allow you to
  ;; compose these.

  (define (conj/R goal)
    (match goal
      [(>> Γ (is-true (conj p q)))
       (subgoals
        ((X (>> Γ (is-true p)))
         (Y (>> Γ (is-true q))))
        (pair ($$ X Γ) ($$ Y Γ)))]))

  (define (disj/R/1 goal)
    (match goal
      [(>> Γ (is-true (disj p q)))
       (subgoals
        ((X (>> Γ (is-true p))))
        (inl ($$ X Γ)))]))

  (define (disj/R/2 goal)
    (match goal
      [(>> Γ (is-true (disj p q)))
       (subgoals
        ((X (>> Γ (is-true q))))
        (inr ($$ X Γ)))]))


  (define ((imp/R x) goal)
    (match goal
      [(>> Γ (is-true (imp p q)))
       (let ([Γ/p (λ (x) (ctx-set Γ x (Π () (is-true p))))])
         (subgoals
          ((X (>> (Γ/p x) (is-true q))))
          (lam (x) ($$ X (Γ/p x)))))]))

  (define (T/R goal)
    (match goal
      [(>> Γ (is-true (T)))
       (subgoals () (nil))]))

  (define ((F/E x) goal)
    (match goal
      [(>> (with-hyp Γ0 (x (Π () (F))) Γ1) (is-true p))
       (subgoals () (nil))]))

  (let* ([x (fresh)]
         [Γ (list (cons x (Π () (is-true (F)))))])
    ((F/E x) (>> Γ (is-true (F)))))


  (conj/R (>> '() (is-true (conj (T) (F)))))
  ((imp/R (fresh)) (>> '() (is-true (imp (F) (T))))))
