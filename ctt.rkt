#lang racket/base

(require
  (for-syntax
   racket/base
   syntax/parse)
  racket/match
  "locally-nameless.rkt"
  "logical-framework.rkt"
  "refinement-engine.rkt")

(define-signature CTT
  ; sorts
  (tm () (SORT))
  (triv () (SORT))
  (cfg () (SORT))

  ; machine configurations
  (cut
   ([e (arity () (tm))]
    [π (arity ([x (arity () (tm))]) (tm))])
   (cfg))

  ; canonical type formers
  (unit () (tm))
  (void () (tm))
  (bool () (tm))
  (equ
   ([A (arity () (tm))]
    [e1 (arity () (tm))]
    [e2 (arity () (tm))])
   (tm))
  (dfun
   ([A (arity () (tm))]
    [B (arity ([x (arity () (tm))]) (tm))])
   (tm))
  (dsum
   ([A (arity () (tm))]
    [B (arity ([x (arity () (tm))]) (tm))])
   (tm))

  ; canonical term formers
  (ax () (triv))
  (tt () (tm))
  (ff () (tm))
  (pair
   ([e1 (arity () (tm))]
    [e2 (arity () (tm))])
   (tm))
  (lam
   ([e (arity ([x (arity () (tm))]) (tm))])
   (tm))

  ; non-canonical term formers
  (bool-if
   ([b (arity () (tm))]
    [e1 (arity () (tm))]
    [e2 (arity () (tm))])
   (tm))
  (fst
   ([e (arity () (tm))])
   (tm))
  (snd
   ([e (arity () (tm))])
   (tm))
  (ap
   ([e1 (arity () (tm))]
    [e2 (arity () (tm))])
   (tm)))

(define-signature JDG
  (eq-ty
   ([A (arity () (tm))]
    [B (arity () (tm))])
   (triv))
  
  (is-inh
   ([A (arity () (tm))])
   (tm))

  (is-eq
   ([e1 (arity () (tm))]
    [e2 (arity () (tm))]
    [A (arity () (tm))])
   (triv)))


(define (ret e)
  (cut e (x) (plug x)))

(define (step C)
  (match C
    [(cut (tt) (x) (bool-if (plug x) e1 e2))
     (ret e1)]
    [(cut (ff) (x) (bool-if (plug x) e1 e2))
     (ret e2)]
    [(cut (lam (y) e1) (x) (ap (plug x) e2))
     (ret (subst ([y () e2]) e1))]
    [(cut (pair e1 e2) (x) (fst (plug x)))
     (ret e1)]
    [(cut (fst e) (x) π)
     (cut e (y) (subst ([x () (fst (plug y))]) π))]
    [(cut (snd e) (x) π)
     (cut e (y) (subst ([x () (snd (plug y))]) π))]
    [(cut (ap e1 e2) (x) π)
     (cut e1 (y) (subst ([x () (ap (plug y) e2)]) π))]
    [(cut (bool-if e1 e2 e3) (x) π)
     (cut e1 (y) (subst ([x () (bool-if (plug y) e2 e3)]) π))]
    [_ null]))

(define (final? C)
  (match C
    [(cut e (x) (plug x))
     (match e
       [(ax) #t]
       [(tt) #t]
       [(ff) #t]
       [(pair e1 e2) #t]
       [(lam (x) e) #t]
       [_ #f])]
    [_ #f]))

(define (steps C)
  (match (step C)
    ['() C]
    [D (steps D)]))

(define (eval e)
  (match (steps (cut e (x) (plug x)))
    [(cut e2 (x) π)
     (subst ([x () e2]) π)]))

(define-rule unit/F
  (>> Γ (eq-ty (unit) (unit)))
  ()
  (ax))

(define-rule bool/F
  (>> Γ (eq-ty (bool) (bool)))
  ()
  (ax))

(define-rule dfun/F
  (>> Γ (eq-ty (dfun A1 (x1) B1x1) (dfun A2 (x2) B1x2)))
  ([X (>> Γ (eq-ty A1 A2))]
   [Y (>> (ctx-set Γ x1 (is-inh A1))
          (eq-ty B1x1 (subst ([x2 () x1]) B1x2)))])
  (ax))

(define-rule dsum/F
  (>> Γ (eq-ty (dsum A1 (x1) B1x1) (dsum A2 (x2) B1x2)))
  ([X (>> Γ (eq-ty A1 A2))]
   [Y (>> (ctx-set Γ x1 (is-inh A1))
          (eq-ty B1x1 (subst ([x2 () x1]) B1x2)))])
  (ax))

(define-rule unit/R
  (>> Γ (is-inh unit))
  ()
  (ax))

(define-rule bool/R/1
  (>> Γ (is-inh bool))
  ()
  (tt))

(define-rule bool/R/2
  (>> Γ (is-inh bool))
  ()
  (ff))

(define-rule (bool/L/inh z) #:sig CTT JDG
  (>> (and Γ (with-hyp Γ0 z  () (is-inh (bool)) Γ1))
      (is-inh (unapply C z)))
  (define Γ/tt (splice-context Γ0 ([z (is-inh (bool))]) (Γ1 (tt))))
  (define Γ/ff (splice-context Γ0 ([z (is-inh (bool))]) (Γ1 (ff))))
  ([X (>> Γ/tt (is-inh (C (tt))))]
   [Y (>> Γ/ff (is-inh (C (ff))))]
   [Z (>> Γ (eq-ty (C z) (C z)))])
  (bool-if (plug z) (plug* X Γ/tt) (plug* X Γ/ff)))

(define-rule (bool/L/eq-ty z) #:sig CTT JDG
  (>> (and Γ (with-hyp Γ0 z  () (is-inh (bool)) Γ1))
      (eq-ty (unapply A1 z) (unapply A2 z)))
  (define Γ/tt (splice-context Γ0 ([z (is-inh (bool))]) (Γ1 (tt))))
  (define Γ/ff (splice-context Γ0 ([z (is-inh (bool))]) (Γ1 (ff))))
  ([X (>> Γ/tt (eq-ty (A1 (tt)) (A2 (tt))))]
   [Y (>> Γ/ff (eq-ty (A1 (ff)) (A2 (ff))))])
  (ax))


(define-rule (dfun/R x) #:sig CTT JDG
  (>> Γ (is-inh (dfun A (y) By)))
  (define (ΓA x) (ctx-set Γ x (is-inh A)))
  ([X (>> (ΓA x) (is-inh (subst ([y () x]) By)))]
   [Y (>> Γ (eq-ty A A))])
  (lam (x) (plug* X (ΓA x))))

(define-rule dsum/R #:sig CTT JDG
  (>> Γ (is-inh (dsum A (x) Bx)))
  ([X (>> Γ (is-inh A))]
   [Y (>> Γ (is-inh (subst ([x () (plug* X Γ)]) Bx)))]
   [Z (>> (ctx-set Γ x (is-inh A))
          (eq-ty Bx Bx))])
  (pair (plug* X Γ) (plug* Y Γ)))


(define-rule ax/eq #:sig CTT JDG
  (>> Γ (is-eq (ax) (ax) (unit)))
  ()
  (ax))

(define-rule tt/eq #:sig CTT JDG
  (>> Γ (is-eq (tt) (tt) (bool)))
  ()
  (ax))

(define-rule ff/eq #:sig CTT JDG
  (>> Γ (is-eq (ff) (ff) (bool)))
  ()
  (ax))

(define-rule (lam/eq x) #:sig CTT JDG
  (>> Γ (is-eq (lam (x1) e1x1) (lam (x2) e2x2) (dfun A (x3) Bx3)))
  (define (ΓA x) (ctx-set Γ x (is-inh A)))
  ([X (>> (ΓA x)
          (is-eq
           (subst ([x1 () x]) e1x1)
           (subst ([x2 () x]) e2x2)
           (subst ([x3 () x]) Bx3)))]
   [Y (>> Γ (eq-ty A A))])
  (ax))

(define-rule pair/eq #:sig CTT JDG
  (>> Γ (is-eq (pair e10 e20) (pair e11 e21) (dsum A (x) Bx)))
  ([X (>> Γ (is-eq e10 e11 A))]
   [Y (>> Γ (is-eq e20 e21 (subst ([x () e10]) Bx)))]
   [Z (>> (ctx-set Γ x (is-inh A))
          (eq-ty Bx Bx))])
  (ax))

(define-rule eq/direct-computation #:sig CTT JDG
  (>> Γ (is-eq e1 e2 A))
  ([X (>> Γ (is-eq (eval e1) (eval e2) (eval A)))])
  (plug* X Γ))

(define-rule eq-ty/direct-computation #:sig CTT JDG
  (>> Γ (eq-ty A1 A2))
  ([X (>> Γ (eq-ty (eval A1) (eval A2)))])
  (plug* X Γ))

(define-rule inh/direct-computation #:sig CTT JDG
  (>> Γ (is-inh A))
  ([X (>> Γ (is-inh (eval A)))])
  (plug* X Γ))

(define-rule (hyp x) #:sig CTT JDG
  (>> (and Γ (with-hyp Γ0 x () tyx Γ1)) goalTy)
  (if (not (equal? goalTy tyx))
      (raise-refinement-error
       (format "Hypothesis mismatch ~a has type ~a, but expected ~a" x tyx goalTy)
       goalTy)
      '())
  ()
  (plug x))


(module+ test
  (define x (fresh "x"))

  (define direct-computation
    (orelse
     inh/direct-computation
     eq-ty/direct-computation))

  (define (bool/L x)
    (orelse
     (bool/L/inh x)
     (bool/L/eq-ty x)))


  (define-syntax (match-goal stx)
    (syntax-parse stx
      [(_ [p:expr m:expr] ...)
       (syntax/loc stx
         (λ (goal)
           ((match goal
              [p m]
              ...)
            goal)))]))


  (define (compute-and t)
    (multicut
     direct-computation
     t))


  (define (try t)
    (orelse t id-tac))

  ; a crappy auto tactic, as a demonstration. A serious one would look a bit different, and do some very
  ; clever stuff about neutral terms.
  (define auto
    (compute-and
     (match-goal
      [(>> Γ (eq-ty (bool) (bool)))
       bool/F]
      [(>> Γ (eq-ty (unit) (unit)))
       unit/F]
      [(>> Γ (eq-ty (bool-if (plug x) _ _) _))
       (multicut (bool/L/eq-ty x) (try auto) (try auto))])))

 
  (define-syntax (lam/t stx)
    (syntax-parse stx
      [(_ (x:id) tac:expr)
       (syntax/loc stx
         (let ([x (fresh)])
           (multicut
            (dfun/R x)
            tac
            auto)))]))

  
  (define (if/t x t1 t2)
    (multicut (bool/L x) t1 t2 auto))
 
  (define my-script
    (lam/t
     (x)
     (if/t
      x
      (compute-and unit/R)
      (compute-and (hyp x)))))
  
  (define goal
    (>> null
        (is-inh (dfun (bool) (x) (bool-if x (unit) (bool))))))

  (my-script goal))

; TODO: define left rules
; TODO: define member equality rules
; TODO: define direct computation rules
