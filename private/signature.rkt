#lang racket/base

(require
 "ast.rkt"
 (prefix-in syn: "syntax.rkt")
 "typecheck.rkt"
 racket/match
 (for-syntax racket/base syntax/parse))

(provide #;extend-sig define-sig
         )

(begin-for-syntax
  (define-syntax-class signature-elem
    (pattern (name:id ((arg:id type:Arity) ...) result)))
  (define-syntax-class Arity
    #:literals (arity)
    ;; TODO: Add another pattern here to add implicit Pi when not used directly?
    (pattern
     (arity () result)
     #:attr (arg 1) '())
    (pattern
     (arity ((arg:id type) ...) result))
    (pattern
     result
     #:attr (arg 1) '())))

(define-syntax (define-constructor stx)
  (syntax-parse stx
    [(_ Σ-in Σ-out c:signature-elem)
     (syntax
      (begin
        (define Ψ
          (let ([t (syn:arity ([c.arg c.type] ...) c.result)])
            (well-formed-classifier Σ-in t)
            (cons-tele 'c.name t (lambda (c.name) (empty-tele)))))
        (define Σ-out (extend-context Σ-in Ψ))
        (define-sig-helper c.name (var Ψ 0) ([c.arg c.type] ...))))]))

(define-syntax (define-sig stx)
  (syntax-parse stx
    [(_ Σ:id #:extends Γ)
     #'(define Σ Γ)]
    [(_ Σ:id #:extends Γ c0:signature-elem c ...)
     (syntax
      (begin
        (define-constructor Γ Σ* c0)
        (define-sig Σ #:extends Σ* c ...)))]
    [(_ Σ:id c ...)
     #'(define-sig Σ #:extends empty-ctx c ...)]))

(define-syntax (define-sig-helper stx)
  (syntax-parse stx
    [(_ name var ((arg type:Arity) ...))
     (define args (syntax->list #'((arg (type.arg ...)) ...)))
     (with-syntax ([(lhs ...)
                    (apply append
                           (for/list ([name/inner args])
                             (syntax-case name/inner ()
                               [(x ())
                                (list #'x)]
                               [(x (y ...))
                                (list #'(y ...) #'x)])))]
                   [(rhs ...)
                    (for/list ([name/inner args])
                      (syntax-case name/inner ()
                        [(x (y ...))
                         #'(syn:bind (y ...) x)]))])
       #'(begin
           (define-for-syntax (help-pattern-expander stx)
             (syntax-parse stx
               [(_ lhs ...)
                (with-syntax ([name-str (symbol->string (syntax->datum #'name))])
                  (syntax/loc stx
                    (app unwrap-nullary
                         (? plug?
                            (app plug-var (? (lambda (m) ((match-equality-test) m var))))
                            (app plug-spine (list rhs ...))))))]))
           (define-for-syntax (help-constructor-expander stx)
             (syntax-parse stx
               [(_ lhs ...)
                (with-syntax ([name-str (symbol->string (syntax->datum #'name))])
                  (syntax/loc stx
                    (syn:plug var
                              rhs
                              ...)))]))
           (define-match-expander name help-pattern-expander help-constructor-expander)))]))


  
