#lang racket/base

(require (for-syntax racket/base syntax/parse racket/match) racket/match racket/splicing)

(require (prefix-in ast: "ast.rkt")
         "typecheck.rkt")

(provide define-sig term arity SORT bind)


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

 (define (get-runtime-sig-arities id)
   (define-values (ct-binding rt-binding) (syntax-local-value/immediate id))
   (unless (sig? ct-binding)
     (raise-syntax-error (syntax-e id) "Not a signature"))
   (sig-arities ct-binding))

 (define (get-runtime-sig-name id)
   (define-values (ct-binding rt-binding) (syntax-local-value/immediate id))
   (unless (sig? ct-binding)
     (raise-syntax-error (syntax-e id) "Not a signature"))
   (sig-runtime ct-binding))

 (define (get-arity Σ op)
   (match (assv op (sig-arities Σ))
     [#f (raise-syntax-error op "Unknown op")]
     [(cons _ arity) arity]))
 )



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
       (define-extended-sig Σ empty-sig c ...))]))

(define-for-syntax (arity-arg-count stx)
  (syntax-parse stx
    [a:Arity
     (length (syntax->list #'(a.type ...)))]))



(define-syntax (define-extended-sig stx)
  (syntax-parse stx
    [(_ Σ:id Σ-old:id)
     (with-syntax ([ar (get-runtime-sig-arities #'Σ-old)]
                   [rt (get-runtime-sig-name #'Σ-old) ])
      #'(define-syntax Σ (sig 'ar #'rt)))]
    [(_ Σ:id Σ-old:id c0:signature-elem c ...)
     (define Σ-old-ar
       (get-runtime-sig-arities #'Σ-old))
     (with-syntax ([(Σ-help) (generate-temporaries #'(Σ))]
                   [Σ-old-rt
                    (get-runtime-sig-name #'Σ-old)]
                   [(Σ-new-rt) (generate-temporaries #'(Σ-new-rt))]
                   [Σ-new-ar
                    (cons (cons (syntax->datum #'c0.name)
                                (map arity-arg-count
                                     (syntax->list #'(c0.type ...))))
                          Σ-old-ar)])
       #'(begin
           (define ty
             (ast:arity (telescope (c0.arg (ast:as-arity (term Σ-old c0.type))) ...)
                        (lambda (c0.arg ...)
                          (term Σ-old c0.result))))
           (well-formed-classifier Σ-old-rt ty)
           (define Ψ
             (ast:snoc-tele (ast:empty-tele) 'c0.name ty))
           (define Σ-new-rt (extend-context Σ-old-rt Ψ))
           (splicing-let-syntax ([Σ-help (sig 'Σ-new-ar #'Σ-new-rt)])
             (define-extended-sig Σ Σ-help c ...))))]))


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

(define-for-syntax (arity->pattern-parser the-sig ar)
  (with-syntax ([Σ (sig-runtime the-sig)])
    (if (pair? ar)
        (if (zero? (car ar))
            (syntax-parser
              [(arg args ...)
               (with-syntax ([(out ...) ((arity->pattern-parser the-sig (cdr ar))
                                         #'(args ...))]
                             [body-pat (parse-term-pattern-expr #'arg the-sig)])
                 #'((? ast:bind?
                       (app ast:bind-vars (list))
                       (app ast:bind-scope body-pat))
                    out
                    ...))])
            (syntax-parser
              [((x:id ...) arg args ...)
               #:when (= (length (syntax->list #'(x ...))) (car ar))
               (with-syntax ([(out ...) ((arity->pattern-parser the-sig (cdr ar))
                                         #'(args ...))]
                             [body-pat (parse-term-pattern-expr #'arg the-sig)])
                 #'((? ast:bind?
                       (app open-bind
                            (list x ...)
                            body-pat))
                    out
                    ...))]))
        (syntax-parser
          [() #'()]))))

(define-for-syntax (arity->syntax-parser signature ar)
  (with-syntax ([Σ (sig-runtime signature)])
    (if (pair? ar)
        (if (zero? (car ar))
            (syntax-parser
              [(arg args ...)
               (with-syntax ([(out ...) ((arity->syntax-parser signature (cdr ar))
                                         #'(args ...))]
                             [sc (parse-term-expr #'arg signature)]
                             [body (parse-term-expr #'arg signature)])
                 #'((ast:bind '() (lambda () (ast:as-plug sc)))
                    out
                    ...))])
            (syntax-parser
              [((x:id ...) arg args ...)
               #:when (= (length (syntax->list #'(x ...))) (car ar))
               (with-syntax ([(out ...) ((arity->syntax-parser signature (cdr ar))
                                         #'(args ...))]
                             [body (parse-term-expr #'arg signature)])
                 #'((ast:bind '(x ...) (lambda (x ...) (ast:as-plug body)))
                    out
                    ...))]))
        (syntax-parser
          [() #'()]))))

(define-for-syntax (parse-term-pattern-expr stx the-sig)
  (syntax-parse stx
    #:literals (unquote SORT arity)
    [SORT
     #'(? ast:SORT?)]
    [(unquote e)
     #'e]
    [(arity ([x t] ...) e)
     (with-syntax ([(tp ...)
                    (map (lambda (p) (parse-term-pattern-expr p the-sig))
                         (syntax->list #'(t ...)))]
                   [body-p
                    (parse-term-pattern-expr #'e the-sig)])
      #'(? ast:arity?
           (app arity-domain (telescope [x tp] ...))
           (app arity-codomain body-p)))]
    [(op:id arg ...)
     (let ([ar (assv (syntax->datum #'op) (sig-arities the-sig))])
       (if ar
           (let ([a (cdr ar)])
             (unless (= (+ (length a) (length (filter (λ (i) (> i 0)) a)))
                        (length (syntax->list #'(arg ...))))
               (raise-syntax-error (syntax->datum #'op) "Wrong number of arguments" #'(op arg ...)))
             (with-syntax ([rt (sig-runtime the-sig)]
                           [(arg-out ...) ((arity->pattern-parser the-sig a) #'(arg ...))])
               #'(? ast:plug?
                   (app ast:plug-var
                        (? (lambda (m) ((match-equality-test) m (var-for-name 'op rt)))))
                   (app ast:plug-spine
                        (list arg-out ...)))))
           (with-syntax ([(arg-p ...) (map (lambda (a) (parse-term-pattern-expr a the-sig))
                                           (syntax->list #'(arg ...)))])
             #'(? ast:plug?
                 (app ast:plug-var op)
                 (app ast:plug-spine
                      (list arg-p ...))))
           #;(raise-syntax-error (syntax->datum #'op) "Unknown operator" stx)
           ))]
    [x:id
     #'x]))



(define-for-syntax (parse-term-expr stx the-sig)
  (syntax-parse stx
    #:literals (unquote SORT arity bind)
    [SORT
     #'(ast:SORT)]
    [(unquote e)
     #'e]
    [(arity ((x t) ...) e)
     (with-syntax ([(t-out ...) (map (lambda (e) (parse-term-expr e the-sig))
                                     (syntax->list #'(t ...)))]
                   [e-out (parse-term-expr #'e the-sig)])
       #'(ast:arity (telescope (x t-out) ...)
                    (lambda (x ...)
                      (ast:as-base-classifier e-out))))]
    [(bind (x:id ...) body)
     (with-syntax ([e-out (parse-term-expr #'body the-sig)])
      #'(ast:bind '(x ...)
                  (lambda (x ...)
                    (ast:as-plug e-out))))]
    [(op:id arg ...)
     (let ([ar (assv (syntax->datum #'op) (sig-arities the-sig))])
       (if ar
           (let ([a (cdr ar)])
             (unless (= (+ (length a) (length (filter (λ (i) (> i 0)) a)))
                        (length (syntax->list #'(arg ...))))
               (raise-syntax-error (syntax->datum #'op) "Wrong number of arguments" #'(op arg ...)))
             (with-syntax ([rt (sig-runtime the-sig)]
                           [(arg-out ...)
                            ((arity->syntax-parser the-sig a)
                             #'(arg ...))])
               #'(ast:plug (var-for-name 'op rt)
                           arg-out ...)))
           (with-syntax ([(arg-e ...) (map (lambda (e) (parse-term-expr e the-sig))
                                           (syntax->list #'(arg ...)))])
             #'(ast:plug op (as-bind arg-e) ...))
           #;(raise-syntax-error (syntax->datum #'op) "Unknown operator" stx)
           ))]
    [x:id
     #'x]))

(define-for-syntax (term-pattern-expander stx)
  (syntax-parse stx
    [(_ Σ e)
     (let-values ([(ct rt) (syntax-local-value/immediate #'Σ)])
       (parse-term-pattern-expr #'e ct))]))

(define-for-syntax (term-expander stx)
  (syntax-parse stx
    [(_ Σ e)
     (let-values ([(ct rt) (syntax-local-value/immediate #'Σ)])
       (parse-term-expr #'e ct))]))

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

  (define id (term Foo (lam (x) x)))

  (check-true
   (ast:var?
    (match id
      [(term Foo (lam (x) (tt))) 1]
      [(term Foo (lam (x) x)) x]
      [(term Foo (lam (x) y)) `(yep ,y)]
      [(term Foo y) y])))

  (define (run e [ρ '()])
    (match e
      [(term Foo (tt)) (term Foo (tt))]
      [(term Foo (ap ,rator ,rand))
       (match* ((run rator ρ) (run rand ρ))
         [((term Foo (lam (x) ,body))
           v)
          (run body (cons (cons x v) ρ))]
         [(other1 other2) (term Foo (ap ,other1 ,other2))])]
      [(term Foo (lam (x) ,any)) e]
      [(term Foo (x))
       (let ([v (assoc x ρ)])
         (if v
             (cdr v)
             x))]))

  (check-true
   (match (run (term Foo (ap (lam (y) y) (tt))))
     [(term Foo (tt)) #t]
     [_ #f]))

  (define foo (telescope (A (ast:SORT)) (B A) (C A) (D A) (E A) (F A)))

  (define-sig Pairs
    (B1 () SORT)
    (B2 () SORT)
    (b1 () (B1))
    (b2 () (B2))
    (Pair ((X SORT) (Y SORT)) SORT)
    (cons ([Q SORT] [Z SORT] [x (Q)] [y (Z)])
          (Pair Q Z))))
