#lang racket

(require "locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt"
         (for-syntax syntax/parse))

(provide (all-defined-out))

(module+ test (require rackunit))

; A little simply-typed evidence semantics. See ctt.rkt for a more advanced example.
(define-signature Lang
  (prop () (SORT))

  (tm () (SORT))

  (conj
   ([p (arity () (prop))]
    [q (arity () (prop))])
   (prop))

  (disj
   ([p (arity () (prop))]
    [q (arity () (prop))])
   (prop))

  (imp
   ([p (arity () (prop))]
    [q (arity () (prop))])
   (prop))

  (T () (prop))

  (F () (prop))

  (nil () (tm))

  (pair
   ([m (arity () (tm))]
    [n (arity () (tm))])
   (tm))

  (fst
   ([m (arity () (tm))])
   (tm))

  (snd
   ([m (arity () (tm))])
   (tm))

  (inl
   ([m (arity () (tm))])
   (tm))

  (inr
   ([m (arity () (tm))])
   (tm))

  (split
   ([m (arity () (tm))]
    [l (arity ([x (tm)]) (tm))]
    [r (arity ([y (tm)]) (tm))]) ; for some reason, I can't use 'x' here. something about duplicate attributes
   (tm))

  (lam
   ([m (arity ([x (tm)]) (tm))])
   (tm)))


(define-signature Jdg
  (is-true
   ([p (arity () (prop))])
   (tm)))


(with-signature
 Lang Jdg
                
 (define-rule (hyp x)
   (>> (with-hyp Γ0 x () tyx Γ1)
       goalTy)
   (if (not (equal? goalTy tyx))
       (raise-refinement-error
        (format "Hypothesis mismatch ~a has type ~a, but expected ~a" x tyx goalTy)
        goalTy)
       '())
   ()
   x)

 (define-rule conj/R
   (>> Γ (is-true (conj p q)))
   ([X (>> Γ (is-true p))]
    [Y (>> Γ (is-true q))])
   (pair (plug* X Γ) (plug* Y Γ)))

 (define-rule (conj/L x x0 x1)
   (>> (with-hyp Γ0 x () (is-true (conj p q)) Γ1)
       (is-true (unapply r x)))
   (define Γ/pq
     (splice-context
      Γ0
      ([x0 (is-true p)] [x1 (is-true q)])
      (Γ1 (pair x0 x1))))
   ([X (>> Γ/pq (is-true (r (pair x0 x1))))])
   (subst
    ([x0 () (fst x)]
     [x1 () (snd x)])
    (plug* X Γ/pq)))

 (define-rule disj/R/1
   (>> Γ (is-true (disj p q)))
   ([X (>> Γ (is-true p))])
   (inl (plug* X Γ)))

 (define-rule disj/R/2
   (>> Γ (is-true (disj p q)))
   ([X (>> Γ (is-true q))])
   (inr (plug* X Γ)))

 (define-rule (disj/L x)
   (>> (with-hyp Γ0 x () (is-true (disj p q)) Γ1)
       (is-true (unapply r x)))
   (define (Γ/p y) (splice-context Γ0 ([y (is-true p)]) (Γ1 (inl y))))
   (define (Γ/q y) (splice-context Γ0 ([y (is-true q)]) (Γ1 (inr y))))
   ([L (>> (Γ/p x) (is-true (r (inl x))))]
    [R (>> (Γ/q x) (is-true (r (inr x))))])
   (split x (xl) (plug* L (Γ/p xl)) (xr) (plug* R (Γ/q xr))))


 (define-rule (imp/R x)
   (>> Γ (is-true (imp p q)))
   (define (Γ/p x)
     (ctx-set Γ x (is-true p)))
   ([X (>> (Γ/p x) (is-true q))])
   (lam (x) (plug* X (Γ/p x))))

 (define-rule T/R
   (>> Γ (is-true (T)))
   ()
   (nil))

 (define-rule (F/L x)
   (>> (with-hyp Γ0 x () (is-true (F)) Γ1)
       (is-true p))
   ()
   (nil)))

(define-syntax (lam/t stx)
  (syntax-parse stx
    [(_ (x:id) t:expr)
     (with-syntax
         ([var-name (symbol->string (syntax->datum #'x))])
       (syntax/loc stx
         (let ([x (fresh var-name)])
           (multicut (imp/R x) t))))]))


(define/contract (split/t x t1 t2)
  (-> free-name? tac/c tac/c
      tac/c)
  (multicut
   (disj/L x)
   t1
   t2))

(define/contract (pair/t t1 t2)
  (-> tac/c tac/c
      tac/c)
  (multicut
   conj/R
   t1
   t2))

(module+ test
  (let* ([goal (>> '() (is-true (conj (disj (T) (F)) (conj (T) (T)))))]
         [script
          (then conj/R (orelse disj/R/1 conj/R) T/R)])
    (check-equal? (proof-extract (script goal))
                  (as-term (pair (inl (nil)) (pair (nil) (nil))))))

  (require (only-in racket/port with-output-to-string))
 
  (check-not-false
   (regexp-match
    ;; This is a hacky regexp that should match a source location, but changes to
    ;; the printing of various structs or source locations may invalidate it.
    ;; The idea is that a probe should have run while executing the test, but
    ;; we can't predict the filename or the gensym used for printing the internal
    ;; names of the >>.
    #rx"refiner-demo\\.rkt:[0-9]+.[0-9]+: #\\(struct:>> \\([^)]+\\)"
    (with-output-to-string
     (λ ()
       (check-equal?
        (let* ([goal (>> '() (is-true (imp (disj (T) (F)) (conj (T) (T)))))]
               [script
                (lam/t (x)
                       (multicut
                        probe
                        (split/t x (pair/t (hyp x) T/R) (orelse T/R (F/L x)))))])
          (proof-extract (script goal)))
        (bind ()
              (lam (x)
                   (split x
                          (b) (pair b (nil))
                          (b) (nil))))))))))
