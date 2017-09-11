#lang racket/base

(require (for-syntax racket/base syntax/parse racket/match) racket/match racket/splicing racket/stxparam)

(require (prefix-in ast: "ast.rkt")
         "typecheck.rkt")

(provide define-sig term arity SORT bind current-signature with-signature)


(module+ test
  (require rackunit))

(define (loose-equal? e1 e2)
  (if (and (ast:lf? e1) (ast:lf? e2))
      (let ([x (ast:as-arity e1)]
            [y (ast:as-arity e2)])
        (equal? x y))
      (equal? e1 e2)))

(match-equality-test loose-equal?)

(begin-for-syntax
 (struct sig (arities runtime)
   #:property prop:rename-transformer
   (lambda (s)
     (syntax-property (sig-runtime s) 'not-free-identifier=? #t)))

 (define (get-runtime-sig-arities)
   (sig-arities (get-current-signature)))

 (define (get-runtime-sig-name)
   (sig-runtime (get-current-signature)))

 (define (get-arity op)
   (match (assv op (sig-arities (get-current-signature)))
     [#f (raise-syntax-error op "Unknown op")]
     [(cons _ arity) arity])))

(define-syntax-parameter current-signature #f)

(define-for-syntax (get-current-signature)
  (define s (syntax-parameter-value #'current-signature))
  (if (not (sig? s))
      (raise-syntax-error 'current-signature "Not a signature")
      s))

(define-syntax (with-signature stx)
  (syntax-parse stx
    [(_ Σ:id e ...)
     (define-values (ct-binding rt-binding) (syntax-local-value/immediate #'Σ))
     (unless (sig? ct-binding)
       (raise-syntax-error (syntax-e #'Σ) "Not a signature"))
     #'(splicing-syntax-parameterize ([current-signature
                                       (let-values ([(ct-binding rt-binding)
                                                     (syntax-local-value/immediate #'Σ)])
                                         ct-binding)])
         e ...)]))

(define-syntax (arity stx)
  (raise-syntax-error 'arity "Used outside of term" stx))

(define-syntax (bind stx)
  (raise-syntax-error 'bind "Used outside of term" stx))

(define-syntax (SORT stx)
  (raise-syntax-error 'SORT "Used outside of term" stx))

(define-syntax empty-sig (sig '() #'empty-ctx))

(begin-for-syntax
  (define-syntax-class signature-elem
    (pattern (name:id ((arg:id type:Arity) ...) result)))
  (define-syntax-class Arity
    #:literals (arity)
    (pattern
     (arity () result)
     #:attr (arg 1) '()
     #:attr (type 1) '())
    (pattern
     (arity ((arg:id type) ...) result))
    (pattern
     result
     #:attr (arg 1) '()
     #:attr (type 1) '())))


(define-syntax (define-sig stx)
  (syntax-parse stx
    [(_ Σ:id c:signature-elem ...)
     (syntax
      (with-signature empty-sig
        (define-extended-sig Σ c ...)))]))

(define-for-syntax (arity-arg-count stx)
  (syntax-parse stx
    [a:Arity
     (length (syntax->list #'(a.type ...)))]))



(define-syntax (define-extended-sig stx)
  (syntax-parse stx
    [(_ Σ:id)
     (with-syntax ([ar (get-runtime-sig-arities)]
                   [rt (get-runtime-sig-name) ])
      #'(define-syntax Σ (sig 'ar #'rt)))]
    [(_ Σ:id c0:signature-elem c ...)
     (define Σ-old-ar
       (get-runtime-sig-arities))
     (with-syntax ([(Σ-help) (generate-temporaries #'(Σ))]
                   [Σ-old-rt
                    (get-runtime-sig-name)]
                   [(Σ-new-rt) (generate-temporaries #'(Σ-new-rt))]
                   [Σ-new-ar
                    (cons (cons (syntax->datum #'c0.name)
                                (map arity-arg-count
                                     (syntax->list #'(c0.type ...))))
                          Σ-old-ar)])
       #'(begin
           (define ty
             (ast:arity (telescope (c0.arg (ast:as-arity (term c0.type))) ...)
                        (lambda (c0.arg ...)
                          (term c0.result))))
           (well-formed-classifier Σ-old-rt ty)
           (define Ψ
             (ast:snoc-tele (ast:empty-tele) 'c0.name ty))
           (define Σ-new-rt (extend-context Σ-old-rt Ψ))
           (splicing-let-syntax ([Σ-help (sig 'Σ-new-ar #'Σ-new-rt)])
             (with-signature Σ-help
              (define-extended-sig Σ c ...)))))]))


(define-match-expander telescope
  (λ (stx)
    (syntax-parse stx
      [(_) (syntax/loc stx (? ast:empty-tele?))]
      [(_ (x:id ty) ... (x0:id ty0))
       (syntax/loc stx
         (? ast:snoc-tele?
            (and (app open-snoc-tele
                      (telescope (x:id ty) ...)
                      x0
                      ty0))))]))
  (λ (stx)
    (syntax-parse stx
      [(_) (syntax/loc stx
             (ast:empty-tele))]
      [(_  (x:id ty) ... (x0:id ty0))
       (syntax/loc stx
         (let ([prev (telescope (x ty) ...)])
           (match-let ([(list x ...)
                        (map (λ (Φ) (ast:var Φ 0))
                             (ast:telescope->list prev))])
            (ast:snoc-tele prev 'x0 (ast:as-arity ty0)))))])))

(define (var-for-name x ctx)
  (let loop ([Ψs (context->list ctx)])
    (if (null? Ψs)
        (error (format "Not found: ~a" x))
        (let ([v (var-for-name/tele x (car Ψs))])
          (if v
              v
              (loop (cdr Ψs)))))))

(define (var-for-name/tele x tele)
  (cond [(ast:empty-tele? tele) #f]
        [(ast:snoc-tele? tele)
         (if (eqv? x (ast:snoc-tele-name tele))
             (ast:var tele 0)
             (var-for-name/tele x (ast:snoc-tele-prev tele)))]))

(define (open-bind b)
  (define vars (for/list ([x (ast:bind-vars b)]
                          [i (in-naturals)])
                 (ast:var b i)))
  (define sc (ast:bind-scope b))
  (values vars sc))

(define-for-syntax (arity->pattern-parser ar)
  (with-syntax ([Σ (get-runtime-sig-name)])
    (if (pair? ar)
        (if (zero? (car ar))
            (syntax-parser
              [(arg args ...)
               (with-syntax ([(out ...) ((arity->pattern-parser (cdr ar))
                                         #'(args ...))]
                             [body-pat (parse-term-pattern-expr #'arg)])
                 #'((? ast:bind?
                       (app ast:bind-vars (list))
                       (app ast:bind-scope body-pat))
                    out
                    ...))])
            (syntax-parser
              [((x:id ...) arg args ...)
               #:when (= (length (syntax->list #'(x ...))) (car ar))
               (with-syntax ([(out ...) ((arity->pattern-parser (cdr ar))
                                         #'(args ...))]
                             [body-pat (parse-term-pattern-expr #'arg)])
                 #'((? ast:bind?
                       (app open-bind
                            (list x ...)
                            body-pat))
                    out
                    ...))]))
        (syntax-parser
          [() #'()]))))

(define-for-syntax (arity->syntax-parser ar)
  (with-syntax ([Σ (get-runtime-sig-name)])
    (if (pair? ar)
        (if (zero? (car ar))
            (syntax-parser
              [(arg args ...)
               (with-syntax ([(out ...) ((arity->syntax-parser (cdr ar))
                                         #'(args ...))]
                             [sc (parse-term-expr #'arg)]
                             [body (parse-term-expr #'arg)])
                 #'((ast:bind '() (lambda () (ast:as-plug sc)))
                    out
                    ...))])
            (syntax-parser
              [((x:id ...) arg args ...)
               #:when (= (length (syntax->list #'(x ...))) (car ar))
               (with-syntax ([(out ...) ((arity->syntax-parser (cdr ar))
                                         #'(args ...))]
                             [body (parse-term-expr #'arg)])
                 #'((ast:bind '(x ...) (lambda (x ...) (ast:as-plug body)))
                    out
                    ...))]))
        (syntax-parser
          [() #'()]))))

(define-for-syntax (parse-term-pattern-expr stx)
  (syntax-parse stx
    #:literals (unquote SORT arity)
    [SORT
     #'(? ast:SORT?)]
    [(unquote e)
     #'e]
    [(arity ([x t] ...) e)
     (with-syntax ([(tp ...)
                    (map (lambda (p) (parse-term-pattern-expr p))
                         (syntax->list #'(t ...)))]
                   [body-p
                    (parse-term-pattern-expr #'e)])
      #'(? ast:arity?
           (app arity-domain (telescope [x tp] ...))
           (app arity-codomain body-p)))]
    [(op:id arg ...)
     (let ([ar (assv (syntax->datum #'op) (get-runtime-sig-arities))])
       (if ar
           (let ([a (cdr ar)])
             (unless (= (+ (length a) (length (filter (λ (i) (> i 0)) a)))
                        (length (syntax->list #'(arg ...))))
               (raise-syntax-error (syntax->datum #'op) "Wrong number of arguments" #'(op arg ...)))
             (with-syntax ([rt (get-runtime-sig-name)]
                           [(arg-out ...) ((arity->pattern-parser a) #'(arg ...))])
               #'(? ast:plug?
                   (app ast:plug-var
                        (? (lambda (m) ((match-equality-test) m (var-for-name 'op rt)))))
                   (app ast:plug-spine
                        (list arg-out ...)))))
           (with-syntax ([(arg-p ...) (map (lambda (a) (parse-term-pattern-expr a))
                                           (syntax->list #'(arg ...)))])
             #'(? ast:plug?
                 (app ast:plug-var op)
                 (app ast:plug-spine
                      (list arg-p ...))))
           #;(raise-syntax-error (syntax->datum #'op) "Unknown operator" stx)
           ))]
    [x:id
     #'x]))



(define-for-syntax (parse-term-expr stx)
  (syntax-parse stx
    #:literals (unquote SORT arity bind)
    [SORT
     #'(ast:SORT)]
    [(unquote e)
     #'e]
    [(arity ((x t) ...) e)
     (with-syntax ([(t-out ...) (map (lambda (e) (parse-term-expr e))
                                     (syntax->list #'(t ...)))]
                   [e-out (parse-term-expr #'e)])
       #'(ast:arity (telescope (x t-out) ...)
                    (lambda (x ...)
                      (ast:as-base-classifier e-out))))]
    [(arity e ...)
     (raise-syntax-error 'arity "Bad arity")]
    [(bind (x:id ...) body)
     (with-syntax ([e-out (parse-term-expr #'body)])
      #'(ast:bind '(x ...)
                  (lambda (x ...)
                    (ast:as-plug e-out))))]
    [(op:id arg ...)
     (let ([ar (assv (syntax->datum #'op) (get-runtime-sig-arities))])
       (if ar
           (let ([a (cdr ar)])
             (unless (= (+ (length a) (length (filter (λ (i) (> i 0)) a)))
                        (length (syntax->list #'(arg ...))))
               (raise-syntax-error (syntax->datum #'op) "Wrong number of arguments" #'(op arg ...)))
             (with-syntax ([rt (get-runtime-sig-name)]
                           [(arg-out ...)
                            ((arity->syntax-parser a)
                             #'(arg ...))])
               #'(ast:plug (var-for-name 'op rt)
                           arg-out ...)))
           (with-syntax ([(arg-e ...) (map (lambda (e) (parse-term-expr e))
                                           (syntax->list #'(arg ...)))])
             #'(ast:plug op (as-bind arg-e) ...))
           #;(raise-syntax-error (syntax->datum #'op) "Unknown operator" stx)
           ))]
    [x:id
     #'x]))

(define-for-syntax (term-pattern-expander stx)
  (syntax-parse stx
    [(_ e)
     (parse-term-pattern-expr #'e)]))

(define-for-syntax (term-expander stx)
  (syntax-parse stx
    [(_ e)
     (parse-term-expr #'e)]))

(define-match-expander term term-pattern-expander term-expander)





(module+ test
  (define-sig Foo
    [Expr ()
          SORT]
    [tt ()
        (Expr)]
    [ap ([rator (Expr)]
         [rand (Expr)])
        (Expr)]
    [lam ([body (arity ([x (Expr)]) (Expr))])
         (Expr)])

  (with-signature Foo
    (define id (term (lam (x) x)))

    (check-true
     (ast:var?
      (match id
        [(term (lam (x) (tt))) 1]
        [(term (lam (x) x)) x]
        [(term (lam (x) y)) `(yep ,y)]
        [(term y) y])))

    (define (run e [ρ '()])
      (match e
        [(term (tt)) (term (tt))]
        [(term (ap ,rator ,rand))
         (match* ((run rator ρ) (run rand ρ))
           [((term (lam (x) ,body))
             v)
            (run body (cons (cons x v) ρ))]
           [(other1 other2) (term (ap ,other1 ,other2))])]
        [(term (lam (x) ,any)) e]
        [(term (x))
         (let ([v (assoc x ρ)])
           (if v
               (cdr v)
               x))]))

    (check-true
     (match (run (term (ap (lam (y) y) (tt))))
       [(term (tt)) #t]
       [_ #f])))

  (define foo (telescope (A (ast:SORT)) (B A) (C A) (D A) (E A) (F A)))

  (define-sig Pairs
    (B1 () SORT)
    (B2 () SORT)
    (b1 () (B1))
    (b2 () (B2))
    (Pair ((X SORT) (Y SORT)) SORT)
    (cons ([Q SORT] [Z SORT] [x (Q)] [y (Z)])
          (Pair Q Z))))
