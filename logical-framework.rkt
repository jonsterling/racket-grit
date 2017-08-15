#lang racket/base

(require racket/contract)
(require (prefix-in ast: "private/ast.rkt")
         (only-in "private/ast.rkt"
                  as-arity as-plug as-bind
                  arity? plug? SORT? bind? telescope?
                  plug-var plug-spine
                  subst))
(require "private/typecheck.rkt")
(require "private/signature-syntax.rkt")

(provide define-sig term SORT
         (recontract-out as-arity as-plug as-bind)
         (recontract-out arity? plug? SORT? bind? telescope?)
         (recontract-out plug-var plug-spine))

(module+ test
  (require rackunit racket/match)

  (define-sig Empty)

  (check-equal? (term Empty SORT) (term Empty SORT))

  (check-equal?
   (term Empty (arity ((a SORT) (b a)) b))
   (term Empty (arity ((b SORT) (c b)) c)))

  (define-sig Num
    (nat () SORT)
    (ze () (nat))
    (su ([x (nat)])
        (nat))
    (ifze ((n (nat))
           (z (nat))
           (s (arity ([x (nat)]) (nat))))
          (nat)))

  (well-formed-context Num)


  ; An example of structural recursion over terms,
  ; using the auto-generated patterns
  (define (printer rtm)
    (match rtm
      [(term Num (nat)) "nat"]
      [(term Num (ze)) "ze"]
      [(term Num (su ,e)) (format "su(~a)" (printer e))]
      [(term Num (ifze ,n ,z (x) ,s))
       (format
        "ifze(~a; ~a; ~a.~a)"
        (printer n)
        (printer z)
        (ast:var-name x)
        (printer s))]
      [(term Num (x))
       (printer x)]
      [(? ast:var? x) (ast:var-name x)]))


  (check-equal?
   (synth Num (term Num (ifze (su (su (ze))) (ze) (x) x)))
   (term Num (nat)))

  (check-equal?
   (printer
    (term Num (ifze (su (su (ze)))
                    (ze)
                    (x) (su x))))
   "ifze(su(su(ze)); ze; x.su(x))")

  (match (term Num (ifze (su (su (ze))) (ze) (x) (su x)))
    [(term Num (ifze (su (su n)) z (x) ,s))
     (check-equal? s (term Num (su x)))])


)
