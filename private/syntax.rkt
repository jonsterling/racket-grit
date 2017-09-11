#lang racket/base

(require (prefix-in ast: "ast.rkt")
         (only-in "ast.rkt" lf? as-arity as-plug as-base-classifier))

(require racket/match (for-syntax racket/base racket/list syntax/parse))

(provide bind arity SORT plug)

(define (loose-equal? e1 e2)
  (if (and (lf? e1) (lf? e2))
      (let ([x (as-arity e1)]
            [y (as-arity e2)])
        (equal? x y))
      (equal? e1 e2)))

(match-equality-test loose-equal?)

(define (open-arity ar)
  (define Γ (ast:arity-domain ar))
  (define vars (for/list ([x/t (ast:telescope->alist Γ)]
                          [i (in-naturals)])
                 (ast:var x/t i)))
  (define types (for/list ([x/t (ast:arity-domain ar)])
                  (cdr x/t)))
  (define scope (ast:arity-codomain ar))
  (values vars types scope))

(define (open-cons-tele t)
  (values
   (ast:var t 0)
   (ast:cons-tele-type t)
   (ast:cons-tele-telescope t)))

(define-match-expander telescope
  (λ (stx)
    (syntax-parse stx
      [(_) (syntax/loc stx (? ast:empty-tele?))]
      [(_ (x0:id ty0) (x:id ty) ...)
       (syntax/loc stx
         (? ast:cons-tele?
            (and (app open-cons-tele
                      x0
                      ty0
                      (telescope (x:id ty) ...)))))]))
  (λ (stx)
    (syntax-parse stx
      [(_) (syntax/loc stx
             (ast:empty-tele))]
      [(_ (x0:id ty0) (x:id ty) ...)
       (syntax/loc stx
         (ast:cons-tele 'x0 (as-arity ty0) (λ (x0) (telescope (x ty) ...))))])))

(define-match-expander arity
  (lambda (stx)
    (syntax-parse stx
      [(_ ((x:id ty:expr) ...) body:expr)
       (syntax/loc stx
         (? ast:arity?
            (app open-arity
                 (list x ...)
                 (list ty ...)
                 body)))]))
  (lambda (stx)
    (syntax-parse stx
      [(_ ((x:id ty:expr) ...) body:expr)
       (syntax/loc stx
         (ast:arity (telescope (x ty) ...)
                    (lambda (x ...)
                      (as-base-classifier body))))])))

(define-match-expander SORT
  (lambda (stx)
    (syntax-parse stx
      [s:id (syntax/loc stx (ast:SORT))]))
  (lambda (stx)
    (syntax-parse stx
      [s:id (syntax/loc stx (ast:SORT))])))

(define (as-bind e)
  (if (ast:bind? e)
      e
      (ast:bind '() (lambda () (as-plug e)))))

(define (open-bind b)
  (define vars (for/list ([x (ast:bind-vars b)]
                          [i (in-naturals)])
                 (ast:var b i)))
  (define sc (ast:bind-scope b))
  (values vars sc))

(define-match-expander bind
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id ...) body)
       (syntax/loc stx
         (? ast:bind?
            (app open-bind
                 (list x ...)
                 body)))]))
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id ...) body)
       (syntax/loc stx
         (ast:bind (list 'x ...)
                   (λ (x ...)
                     (as-plug body))))])))

(define-match-expander plug
  (lambda (stx)
    (syntax-parse stx
      [(_ x)
       (syntax/loc stx
         (ast:plug x))]
      [(_ x arg ...)
       (syntax/loc stx
         (? ast:plug?
            (and (app ast:plug-var x)
                 (app ast:plug-spine (list arg ...)))))]))
  (lambda (stx)
    (syntax-parse stx
      [(_ x arg ...)
       (syntax/loc stx
         (ast:plug x (as-bind arg) ...))]
      [(_ e)
       (syntax/loc stx
         (as-plug e))])))
