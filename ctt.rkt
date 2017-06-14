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
     (ret (subst ([y e2]) e1))]
    [(cut (pair e1 e2) (x) (fst ($ x)))
     (ret e1)]
    [(cut (fst e) (x) π)
     (cut e (y) (subst ([x (fst ($ y))]) π))]
    [(cut (snd e) (x) π)
     (cut e (y) (subst ([x (snd ($ y))]) π))]
    [(cut (ap e1 e2) (x) π)
     (cut e1 (y) (subst ([x (ap ($ y) e2)]) π))]))

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
   [Y (>> (append Γ `((,x1 . ,A1))) (eq-ty B1x1 (subst ([x2 x1]) B1x2)))])
  (ax))

(define-rule dsum/F
  (>> Γ (eq-ty (dsum A1 (x1) B1x1) (dsum A2 (x2) B1x2)))
  ([X (>> Γ (eq-ty A1 A2))]
   [Y (>> (append Γ `((,x1 . ,A1))) (eq-ty B1x1 (subst ([x2 x1]) B1x2)))])
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

(define-rule dfun/R
  (>> Γ (is-inh (dfun A (x) Bx)))
  (define (ΓA x) (append Γ `((,x . ,A))))
  ([X (>> (ΓA x) (is-inh Bx))]
   [Y (>> Γ (eq-ty A A))])
  (lam (x) ($* X (ΓA x))))

(define-rule dsum/R
  (>> Γ (is-inh (dsum A (x) Bx)))
  ([X (>> Γ (is-inh A))]
   [Y (>> Γ (is-inh (subst ([x ($* X Γ)]) Bx)))])
  (pair ($* X Γ) ($* Y Γ)))

; TODO: define elimination rules
; TODO: define member equalit rules
; TODO: define direct computation rules