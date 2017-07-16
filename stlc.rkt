#lang racket

; This is the example language used in the internals section of the manual

(require "locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt"
         (for-syntax syntax/parse))

(define-signature STLC
  (tm () (SORT))
  (tp () (SORT))

  (lam
   ([m (arity ([x (tm)]) (tm))])
   (tm))

  (app
   ([e1 (arity () (tm))]
    [e2 (arity () (tm))])
   (tm))

  (★ () (tm))

  (unit () (tp))
  (fun
   ([t1 (arity () (tp))]
    [t2 (arity () (tp))])
   (tp)))

(define-signature Jdg
  (truth () (SORT))
  (axiom () (truth))

  (has-type
   ([e (arity () (tm))]
    [t (arity () (tp))])
   (truth)))

(with-signature
  STLC Jdg
  (define-rule star-unit
    (>> Γ (has-type (★) (unit)))
    ()
    (axiom)))
