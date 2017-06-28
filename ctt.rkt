#lang racket/base

(require
  racket/match
  "locally-nameless.rkt"
  "logical-framework.rkt"
  "refinement-engine.rkt")

(define-signature CTT
  ; sorts
  (tm () (TYPE))
  (cfg () (TYPE))

  ; machine configurations
  (cut
   ([e (=> () (tm))]
    [π (=> ([x (=> () (tm))]) (tm))])
   (cfg))

  ; canonical type formers
  (unit () (tm))
  (void () (tm))
  (bool () (tm))
  (equ
   ([A (=> () (tm))]
    [e1 (=> () (tm))]
    [e2 (=> () (tm))])
   (tm))
  (dfun
   ([A (=> () (tm))]
    [B (=> ([x (=> () (tm))]) (tm))])
   (tm))
  (dsum
   ([A (=> () (tm))]
    [B (=> ([x (=> () (tm))]) (tm))])
   (tm))

  ; canonical term formers
  (ax () (tm))
  (tt () (tm))
  (ff () (tm))
  (pair
   ([e1 (=> () (tm))]
    [e2 (=> () (tm))])
   (tm))
  (lam
   ([e (=> ([x (=> () (tm))]) (tm))])
   (tm))

  ; non-canonical term formers
  (bool-if
   ([b (=> () (tm))]
    [e1 (=> () (tm))]
    [e2 (=> () (tm))])
   (tm))
  (fst
   ([e (=> () (tm))])
   (tm))
  (snd
   ([e (=> () (tm))])
   (tm))
  (ap
   ([e1 (=> () (tm))]
    [e2 (=> () (tm))])
   (tm))

  ; forms of judgments
  (eq-ty
   ([A (=> () (tm))]
    [B (=> () (tm))])
   (TYPE))
  
  (is-inh
   ([A (=> () (tm))])
   (TYPE))

  (is-eq
   ([e1 (=> () (tm))]
    [e2 (=> () (tm))]
    [A (=> () (tm))])
   (TYPE)))

(define (ret e)
  (cut e (x) ($ x)))

(define (step C)
  (match C
    [(cut (tt) (x) (bool-if ($ x) e1 e2))
     (ret e1)]
    [(cut (ff) (x) (bool-if ($ x) e1 e2))
     (ret e2)]
    [(cut (lam (y) e1) (x) (ap ($ x) e2))
     (ret (subst ([y (Λ () e2)]) e1))]
    [(cut (pair e1 e2) (x) (fst ($ x)))
     (ret e1)]
    [(cut (fst e) (x) π)
     (cut e (y) (subst ([x (Λ () (fst ($ y)))]) π))]
    [(cut (snd e) (x) π)
     (cut e (y) (subst ([x (Λ () (snd ($ y)))]) π))]
    [(cut (ap e1 e2) (x) π)
     (cut e1 (y) (subst ([x (Λ () (ap ($ y) e2))]) π))]
    [(cut (bool-if e1 e2 e3) (x) π)
     (cut e1 (y) (subst ([x (Λ () (bool-if ($ y) e2 e3))]) π))]
    [_ null]))

(define (final? C)
  (match C
    [(cut e (x) ($ x))
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
  (match (steps (cut e (x) ($ x)))
    [(cut e2 (x) π)
     (subst ([x (Λ () e2)]) π)]))

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
   [Y (>> (append Γ `((,x1 . (=> () (is-inh ,A1)))))
          (eq-ty B1x1 (subst ([x2 x1]) B1x2)))])
  (ax))

(define-rule dsum/F
  (>> Γ (eq-ty (dsum A1 (x1) B1x1) (dsum A2 (x2) B1x2)))
  ([X (>> Γ (eq-ty A1 A2))]
   [Y (>> (append Γ `(((,x1 . (=> () (is-inh ,A1))))))
          (eq-ty B1x1 (subst ([x2 x1]) B1x2)))])
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

(define-rule (bool/L z)
  (>> (and Γ (with-hyp Γ0 (z (=> () (is-inh (bool)))) Γ1))
      (is-inh (unapply C z)))
  (define Γ/tt (append Γ0 `((,z . ,(=> () (is-inh (bool))))) (Γ1 (Λ () (tt)))))
  (define Γ/ff (append Γ0 `((,z . ,(=> () (is-inh (bool))))) (Γ1 (Λ () (ff)))))
  ([X (>> Γ/tt (is-inh (C (Λ () (tt)))))]
   [Y (>> Γ/ff (is-inh (C (Λ () (ff)))))]
   [Z (>> Γ (eq-ty (C z) (C z)))])
  (bool-if ($ z) ($* X Γ/tt) ($* X Γ/ff)))


(define-rule (dfun/R x)
  (>> Γ (is-inh (dfun A (y) By)))
  (define (ΓA x) (append Γ `((,x . ,(=> () (is-inh A))))))
  ([X (>> (ΓA x) (is-inh (subst ([y x]) By)))]
   [Y (>> Γ (eq-ty A A))])
  (lam (x) ($* X (ΓA x))))

(define-rule dsum/R
  (>> Γ (is-inh (dsum A (x) Bx)))
  ([X (>> Γ (is-inh A))]
   [Y (>> Γ (is-inh (subst ([x (Λ () ($* X Γ))]) Bx)))]
   [Z (>> (append Γ `((,x . ,(=> () (is-inh A))))) (eq-ty Bx Bx))])
  (pair ($* X Γ) ($* Y Γ)))


(define-rule ax/eq
  (>> Γ (is-eq (ax) (ax) (unit)))
  ()
  (ax))

(define-rule tt/eq
  (>> Γ (is-eq (tt) (tt) (bool)))
  ()
  (ax))

(define-rule ff/eq
  (>> Γ (is-eq (ff) (ff) (bool)))
  ()
  (ax))

(define-rule (lam/eq x)
  (>> Γ (is-eq (lam (x1) e1x1) (lam (x2) e2x2) (dfun A (x3) Bx3)))
  (define (ΓA x) (append Γ `((,x . ,(=> () (is-inh A))))))
  ([X (>> (ΓA x)
          (is-eq
           (subst ([x1 x]) e1x1)
           (subst ([x2 x]) e2x2)
           (subst ([x3 x]) Bx3)))]
   [Y (>> Γ (eq-ty A A))])
  (ax))

(define-rule pair/eq
  (>> Γ (is-eq (pair e10 e20) (pair e11 e21) (dsum A (x) Bx)))
  ([X (>> Γ (is-eq e10 e11 A))]
   [Y (>> Γ (is-eq e20 e21 (subst ([x (Λ () e10)]) Bx)))]
   [Z (>> (append Γ `((,x . ,(=> () (is-inh A))))) (eq-ty Bx Bx))])
  (ax))

(define-rule eq/direct-computation
  (>> Γ (is-eq e1 e2 A))
  ([X (>> Γ (is-eq (eval e1) (eval e2) (eval A)))])
  ($* X Γ))

(define-rule inh/direct-computation
  (>> Γ (is-inh A))
  ([X (>> Γ (is-inh (eval A)))])
  ($* X Γ))

(define-rule (hyp x)
  (>> (and Γ (with-hyp Γ0 (x (=> () tyx)) Γ1)) goalTy)
  (if (not (equal? goalTy tyx))
      (raise-refinement-error
       (format "Hypothesis mismatch ~a has type ~a, but expected ~a" x tyx goalTy)
       goalTy)
      '())
  ()
  ($ x))


(module+ test
  (define x (fresh "x"))
  
  (define my-script
    (multicut
     (dfun/R x)
     (multicut
      (bool/L x)
      (multicut
       inh/direct-computation
       unit/R)
      (multicut
       inh/direct-computation
       (hyp x))
      ; below, I need a structural equality rule for types formed using bool-if;
      ; probably, at this point we should switch modes to a universe membership
      ; judgment, and then use the (un-written) structural equality rule for bool-if.
      probe)
     bool/F))
  
  (define goal
    (>> null (is-inh (dfun (bool) (x) (bool-if ($ x) (unit) (bool))))))
  (my-script goal))

; TODO: define left rules
; TODO: define member equality rules
; TODO: define direct computation rules