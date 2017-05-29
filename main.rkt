#lang racket/base

(require
 (for-syntax
  racket/base
  racket/list
  syntax/parse
  racket/syntax
  (for-syntax racket/base))
 racket/contract
 racket/fixnum
 racket/function
 racket/list
 racket/match
 racket/provide-syntax
 racket/string
 racket/dict
 "locally-nameless.rkt")


(provide
 TYPE Π Λ $
 chk-rtype
 chk-tele
 chk-ntm
 chk-rtm
 chk-spine
 inf-rtm
 wf-rtype?
 wf-type?
 wf-tele?
 wf-spine?
 wf-ntm?
 wf-rtm?)

(module+ test
  (require rackunit))


(struct Π (domain codomain)
  #:omit-define-syntaxes
  #:extra-constructor-name make-Π
  #:methods gen:custom-write
  ((define (write-proc pi port mode)
     (define tl (Π-domain pi))
     (define sc (Π-codomain pi))
     (match-define (scope vl body) sc)
     (define temps (fresh-print-names vl))
     (fprintf port "{")
     (write-proc/telescope tl port mode)
     (fprintf port "}")
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port " --> ~a" body))))

  #:property prop:bindings
  (binder
   (λ (pi frees i)
     (define tl (Π-domain pi))
     (define sc (Π-codomain pi))
     (match-define (binder abs-tl _) bindings/telescope)
     (match-define (binder abs-sc _) (bindings-accessor sc))
     (make-Π (abs-tl tl frees i) (abs-sc sc frees i)))
   (λ (pi i new-exprs)
     (define tl (Π-domain pi))
     (define sc (Π-codomain pi))
     (match-define (binder _ inst-tl) bindings/telescope)
     (match-define (binder _ inst-sc) (bindings-accessor sc))
     (make-Π (inst-tl tl i new-exprs) (inst-sc sc i new-exprs))))

  #:methods gen:equal+hash
  ((define (equal-proc pi1 pi2 rec-equal?)
     (and
      (rec-equal? (Π-domain pi1) (Π-domain pi2))
      (rec-equal? (Π-codomain pi1) (Π-codomain pi2))))
   (define (hash-proc pi rec-hash)
     (fxxor
      (rec-hash (Π-domain pi))
      (rec-hash (Π-codomain pi))))
   (define (hash2-proc pi rec-hash2)
     (fxxor
      (rec-hash2 (Π-domain pi))
      (rec-hash2 (Π-codomain pi))))))


(define-for-syntax Π-expander
  (λ (stx)
    (syntax-parse stx
      [(_ ((x:id e:expr) ...) cod:expr)
       (syntax/loc stx (PI (telescope (x e) ...) (in-scope (x ...) cod)))])))

(define-match-expander Π
  (λ (stx)
    (syntax-parse stx
      [(_ ((x:id e:expr) ...) cod:expr)
       (syntax/loc stx
         (? Π? (and (app Π-domain (telescope (x e) ...))
                    (app Π-codomain (in-scope (x ...) cod)))))]))
  (λ (stx)
    (syntax-parse stx
      [(_ ((x:id e:expr) ...) cod:expr)
       (syntax/loc stx
         (make-Π (telescope (x e) ...) (in-scope (x ...) cod)))])))

(struct Λ (scope)
  #:omit-define-syntaxes
  #:extra-constructor-name make-Λ
  #:methods gen:custom-write
  ((define (write-proc e port mode)
     (define sc (Λ-scope e))
     (define temps (fresh-print-names (scope-valence sc)))
     (define binder
       (string-join (for/list ([x temps]) (format "~a" x)) ", "))
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port "[~a]~a" binder (scope-body sc)))))

  #:property prop:bindings
  (binder
   (λ (e frees i)
     (define sc (Λ-scope e))
     (match-define (binder abs _) (bindings-accessor sc))
     (make-Λ (abs sc frees i)))
   (λ (e i new-exprs)
     (define sc (Λ-scope e))
     (match-define (binder _ inst) (bindings-accessor sc))
     (make-Λ (inst sc i new-exprs))))


  #:methods gen:equal+hash
  ((define (equal-proc lam1 lam2 rec-equal?)
     (and
      (rec-equal? (Λ-scope lam1) (Λ-scope lam2))))
   (define (hash-proc lam rec-hash)
     (rec-hash (Λ-scope lam)))
   (define (hash2-proc lam rec-hash2)
     (rec-hash2 (Λ-scope lam)))))

(define-match-expander Λ
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (syntax/loc stx (? Λ? (app Λ-scope (in-scope (x ...) body))))]))
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (syntax/loc stx (make-Λ (in-scope (x ...) body)))])))

(struct TYPE ()
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ty port mode)
     (fprintf port "TYPE")))
  #:property prop:bindings
  (binder
   (λ (ty frees i) ty)
   (λ (ty i new-exprs) ty)))

(struct $ (var spine)
  #:omit-define-syntaxes
  #:extra-constructor-name make-$
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ap port mode)
     (define x ($-var ap))
     (define sp ($-spine ap))
     (define spine (string-join (for/list ([x sp]) (format "~a" x))))
     (fprintf port "~a[~a]" x spine)))

  #:property prop:bindings
  (binder
   (λ (ap frees i)
     (define var ($-var ap))
     (define spine ($-spine ap))
     (match-define (binder abs-var _) (bindings-accessor var))
     (define (go arg)
       (match-define (binder abs _) (bindings-accessor arg))
       (abs arg frees i))
     (make-$ (abs-var var frees i) (map go spine)))
   (λ (ap i new-exprs)
     (define var ($-var ap))
     (define spine ($-spine ap))
     (match-define (binder _ inst-var) (bindings-accessor var))
     (define (go-arg arg)
       (match-define (binder _ inst-arg) (bindings-accessor arg))
       (inst-arg arg i new-exprs))
     (define new-spine (map go-arg spine))
     (match (inst-var var i new-exprs)
       [(bound-name ix) (make-$ (bound-name ix) new-spine)]
       [(free-name sym hint) (make-$ (free-name sym hint) new-spine)]
       [(? Λ? (app Λ-scope sc))
        (define body (scope-body sc))
        (match-let ([(binder _ inst-body) (bindings-accessor body)])
          (inst-body body i new-spine))]))))

(define-match-expander $
  (λ (stx)
    (syntax-parse stx
      [(_ x e ...)
       (syntax/loc stx
         (? $?
            (and (app $-var x)
                 (app $-spine (list e ...)))))]))
  (λ (stx)
    (syntax-parse stx
      [(_ x e ...)
       (syntax/loc stx
         (make-$ x (list e ...)))])))

(define-for-syntax sig-expander
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ty:expr) ...)
       (with-syntax ([(x-var ...) (syntax->datum #'(x ...))])
         (syntax/loc stx
           (list (cons (free-name 'x (symbol->string 'x)) ty) ...)))])))

(define-match-expander signature sig-expander sig-expander)


(define-syntax (one-pattern-lhs stx)
  (syntax-parse stx
    #:literals (Π)
    [(_ (x:id (Π () e)))
     (syntax/loc stx
       (x))]
    [(_ (x:id (Π (y1 y ...) e)) elem ...)
     (syntax/loc stx
       ((y1 y ...) x))]))

(define-for-syntax tele-expander
  (λ (stx)
    (define (make-tele bound todo)
      (syntax-parse todo
        [((x:id e:expr) (y:id e2:expr) ...)
         (with-syntax ([bound bound]
                       [rhs (make-tele (append bound (list #'x))
                                       #'((y e2) ...))])
           #'(cons (in-scope bound e)
                   rhs))]
        [() #''()]))
    (syntax-parse stx
      [(_ (x:id e:expr) ...)
       (make-tele '() #'((x e) ...))])))

(define-match-expander telescope
  tele-expander tele-expander)


; a signature/context is an association list

(begin-for-syntax
  (define-syntax-class signature-elem
    (pattern (name:id ((arg:id type:Pi) ...) result)))
  (define-syntax-class Pi
    #:literals (Π)
    ;; TODO: Add another pattern here to add implicit Pi when not used directly?
    (pattern (Π () result)
             #:attr (arg 1) '()
             #:attr nullary? #f)
    (pattern (Π ((arg:id type) ...) result)
             #:attr nullary? #t)))



(define-syntax (define-signature-helper stx)
  (syntax-parse stx
    [(_ name ((arg type:Pi) ...) )
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
                         #'(Λ (y ...) x)]))])
       #'(begin (define-for-syntax (help-expander stx)
                  (syntax-parse stx
                    [(_ lhs ...)
                     (with-syntax ([name-str (symbol->string (syntax->datum #'name))])
                       (syntax/loc stx
                         ($ (free-name 'name name-str)
                            rhs
                            ...)))]))
                (define-match-expander name help-expander help-expander)))]))

(define-syntax (define-signature stx)
  (syntax-parse stx
    [(_ sig-name c:signature-elem ...)
     #'(begin
         (define sig-name
           (signature (c.name (Π ((c.arg c.type) ...) c.result)) ...))
         (define-signature-helper c.name ((c.arg c.type) ...)) ...)]))

(define (snoc xs x)
  (append xs (list x)))

(define ctx?
  (listof (cons/c free-name? Π?)))

(define rtype?
  (or/c TYPE? $?))

(define type? Π?)

(define tele?
  (listof scope?))

(define spine?
  (listof Λ?))

(define/contract (ctx-set ctx x ty)
  (-> ctx? free-name? Π? ctx?)
  (dict-set ctx x ty))

(define/contract (ctx-ref ctx x)
  (-> ctx? free-name? Π?)
  (dict-ref ctx x))

(define/contract (chk-tele ctx tele)
  (-> ctx? tele? (cons/c ctx? (listof free-name?)))
  (define (aux ctx xs tele)
    (match tele
      ['() (cons ctx xs)]
      [(cons sc tele)
       (let* ([x (fresh)]
              [ty (instantiate sc xs)]
              [ctx (ctx-set ctx x ty)]
              [xs (snoc xs x)])
         (chk-type ctx ty)
         (aux ctx xs tele))]))
  (aux ctx '() tele))

(define/contract (wf-tele? ctx)
  (-> ctx? (-> tele? boolean?))
  (λ (tele)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-tele ctx tele)
      #t)))


(define/contract (wf-rtype? ctx)
  (-> ctx? (-> rtype? boolean?))
  (λ (rty)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-rtype ctx rty)
      #t)))

(define/contract (chk-type ctx ty)
  (-> ctx? type? any/c)
  (match ty
    [(? Π? (and (app Π-domain tele) (app Π-codomain cod)))
     (match (chk-tele ctx tele)
       [(cons ctx xs)
        (chk-rtype ctx (instantiate cod xs))])]))


(define/contract (wf-type? ctx)
  (-> ctx? (-> type? boolean?))
  (λ (ty)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-type ctx ty)
      #t)))

(define/contract (chk-rtype ctx rty)
  (-> ctx? rtype? any/c)
  (match rty
    [(TYPE) #t]
    [APP?
     (match (inf-rtm ctx rty)
       [(TYPE) '#t])]))

(define/contract (chk-spine ctx tele spine)
  (->i ((ctx ctx?)
        (tele (ctx) (wf-tele? ctx))
        (spine spine?))
       (result any/c))
  (define (aux ctx env tele spine)
    (match* (tele spine)
      [('() '()) #t]
      [((cons sc tele) (cons ntm spine))
       (chk-ntm ctx ntm (instantiate sc env))
       (aux ctx (snoc env ntm) tele spine)]))
  (aux ctx '() tele spine))


(define/contract (wf-spine? ctx tele)
  (->i ((ctx ctx?)
        (tele (ctx) (wf-tele? ctx)))
       (result (-> spine? boolean?)))
  (λ (spine)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-spine ctx spine tele)
      #t)))

(define/contract (chk-ntm ctx ntm ty)
  (->i ((ctx ctx?)
        (ntm Λ?)
        (ty (ctx ntm) (wf-type? ctx)))
       (result any/c))
  (match* (ntm ty)
    [((? Λ? (app Λ-scope sc)) (? Π? (and (app Π-domain tele) (app Π-codomain cod))))
     (match (chk-tele ctx tele)
       [(cons ctx xs)
        (chk-rtm ctx (instantiate sc xs) (instantiate cod xs))])]))


(define/contract (wf-ntm? ctx ty)
  (->i ((ctx ctx?)
        (ty (ctx) (wf-type? ctx)))
       (result (-> Λ? boolean?)))
  (λ (ntm)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-ntm ctx ntm ty)
      #t)))

(define/contract (inf-rtm ctx rtm)
  (->i ((ctx ctx?)
        (rtm $?))
       (result (ctx rtm) (wf-rtype? ctx)))
  (match rtm
    [(? $? (and (app $-var x) (app $-spine spine)))
     (match (ctx-ref ctx x)
       [(? Π? (and (app Π-domain tele) (app Π-codomain cod)))
        (chk-spine ctx tele spine)
        (instantiate cod spine)])]))

(define/contract (chk-rtm ctx rtm rty)
  (-> ctx? $? rtype? any/c)
  (if (equal? (inf-rtm ctx rtm) rty)
      #t
      (error "Type mismatch")))

(define/contract (wf-rtm? ctx rty)
  (->i ((ctx ctx?)
        (rty (ctx) (wf-rtype? ctx)))
       (result (-> $? boolean?)))
  (λ (rtm)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-rtm ctx rtm rty)
      #t)))



(module+ test
  (let ([x (fresh "hello")])
    (check-equal?
     (Π ((a x) (b ($ a))) ($ b))
     (Π ((b x) (c ($ b))) ($ c))))

  (check-equal?
   (Λ (n m) n)
   (Λ (a b) a))

  (define-signature num-sig
    (nat () (TYPE))
    (ze () (nat))
    (su ((x (Π () (nat))))
        (nat))
    (ifze ((n (Π () (nat)))
           (z (Π () (nat)))
           (s (Π ((x (Π () (nat)))) (nat))))
          (nat)))

  (check-equal?
   (inf-rtm num-sig (ifze (su (su (ze))) (ze) (x) ($ x)))
   (nat))


  (match (ifze (su (su (ze))) (ze) (x) (su ($ x)))
    [(ifze (su (su n)) z (x) s)
     (check-equal? s (su ($ x)))])

  (let ([x (fresh "hi")])
    (check-equal?
     (telescope (y x) (z y))
     (telescope (z x) (z z))))

  (let ([x (fresh "hi")]
        [x* (fresh "hi")])
    (check-not-equal?
     (telescope (y x) (z y))
     (telescope (z x*) (z z))))

  (let ([x (fresh "hi")])
    (check-equal?
     (match (telescope (y x) (z y))
       [(telescope (m v) (n m)) v])
     x)))
