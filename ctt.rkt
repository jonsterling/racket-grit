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
   (tm)))

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
