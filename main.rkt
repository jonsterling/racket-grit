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
 pi-type lambda-op application TYPE
 Π lam)

(module+ test
  (require rackunit))


(struct pi-type (domain codomain)
  #:methods gen:custom-write
  ((define (write-proc pi port mode)
     (match-define (pi-type tl sc) pi)
     (match-define (scope vl body) sc)
     (define temps (fresh-print-names vl))
     (fprintf port "{")
     (write-proc/telescope tl port mode)
     (fprintf port "}")
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port " --> ~a" body))))

  #:property prop:bindings
  (binder
   (lambda (pi frees i)
     (match-define (pi-type tl sc) pi)
     (match-define (binder abs-tl _) bindings/telescope)
     (match-define (binder abs-sc _) (bindings-accessor sc))
     (pi-type (abs-tl tl frees i) (abs-sc sc frees i)))
   (lambda (pi i new-exprs)
     (match-define (pi-type tl sc) pi)
     (match-define (binder _ inst-tl) bindings/telescope)
     (match-define (binder _ inst-sc) (bindings-accessor sc))
     (pi-type (inst-tl tl i new-exprs) (inst-sc sc i new-exprs))))

  #:methods gen:equal+hash
  ((define (equal-proc pi1 pi2 rec-equal?)
     (and
      (rec-equal? (pi-type-domain pi1) (pi-type-domain pi2))
      (rec-equal? (pi-type-codomain pi1) (pi-type-codomain pi2))))
   (define (hash-proc pi rec-hash)
     (fxxor
      (rec-hash (pi-type-domain pi))
      (rec-hash (pi-type-codomain pi))))
   (define (hash2-proc pi rec-hash2)
     (fxxor
      (rec-hash2 (pi-type-domain pi))
      (rec-hash2 (pi-type-codomain pi))))))

(struct lambda-op (scope)
  #:transparent ;; should it be transparent? Not sure. - jms
  #:methods gen:custom-write
  ((define (write-proc lam port mode)
     (match-define (lambda-op sc) lam)
     (define temps (fresh-print-names (scope-valence sc)))
     (define binder
       (string-join (for/list ([x temps]) (format "~a" x)) ", "))
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port "[~a]~a" binder (scope-body sc)))))

  #:property prop:bindings
  (binder
   (lambda (lam frees i)
     (match-define (lambda-op sc) lam)
     (match-define (binder abs _) (bindings-accessor sc))
     (lambda-op (abs sc frees i)))
   (lambda (lam i new-exprs)
     (match-define (lambda-op sc) lam)
     (match-define (binder _ inst) (bindings-accessor sc))
     (lambda-op (inst sc i new-exprs)))))


;; the TYPE type
(struct TYPE ()
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ty port mode)
     (fprintf port "TYPE")))
  #:property prop:bindings
  (binder
   (lambda (ty frees i) ty)
   (lambda (ty i new-exprs) ty)))

(struct application (var spine)
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ap port mode)
     (match-define (application x sp) ap)
     (define spine (string-join (for/list ([x sp]) (format "~a" x))))
     (fprintf port "~a[~a]" x spine)))

  #:property prop:bindings
  (binder
   (lambda (ap frees i)
     (match-define (application var spine) ap)
     (match-define (binder abs-var _) (bindings-accessor var))
     (define (go arg)
       (match-define (binder abs _) (bindings-accessor arg))
       (abs arg frees i))
     (application (abs-var var frees i) (map go spine)))
   (lambda (ap i new-exprs)
     (match-define (application var spine) ap)
     (match-define (binder _ inst-var) (bindings-accessor var))
     (define (go-arg arg)
       (match-define (binder _ inst-arg) (bindings-accessor arg))
       (inst-arg arg i new-exprs))
     (define new-spine (map go-arg spine))
     (match (inst-var var i new-exprs)
       [(bound-name ix) (application (bound-name ix) new-spine)]
       [(free-name sym hint) (application (free-name sym hint) new-spine)]
       [(lambda-op sc)
        (define body (scope-body sc))
        (match-let ([(binder _ inst-body) (bindings-accessor body)])
          (inst-body body i new-spine))]))))

(define-match-expander in-scope
  ; destructor
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (with-syntax ([var-count (length (syntax->list #'(x ...)))])
         #'(? (lambda (sc) (and (scope? sc) (= (scope-valence sc) var-count)))
              (app auto-inst (cons (list x ...) body))))]))

  ; constructor
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (with-syntax ([(x-str ...) (map symbol->string (syntax->datum #'(x ...)))])
         (syntax/loc stx
           (let ([x (fresh x-str)] ...)
             (abs (list x ...) body))))])))


(define-for-syntax sig-expander
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id ty:expr) ...)
       (with-syntax ([(x-var ...) (syntax->datum #'(x ...))])
         (syntax/loc stx
           (list (cons (free-name 'x (symbol->string 'x)) ty) ...)))])))

(define-match-expander signature sig-expander sig-expander)

(define-for-syntax tele-expander
  (lambda (stx)
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

(define-for-syntax Π-expander
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id e:expr) ... cod:expr)
       (syntax/loc stx (pi-type (telescope (x e) ...) (in-scope (x ...) cod)))])))

(define-match-expander Π Π-expander Π-expander)

(define-for-syntax lam-expander
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (syntax/loc stx (lambda-op (in-scope (x ...) body)))])))

(define-match-expander lam lam-expander lam-expander)

(define-for-syntax $-expander
  (lambda (stx)
    (syntax-parse stx
      [(_ x:expr e:expr ...)
       (syntax/loc stx (application x (list e ...)))])))

(define-match-expander $ $-expander $-expander)


; a signature/context is an association list

(define (snoc xs x)
  (append xs (list x)))

(define ctx?
  (listof (cons/c free-name? pi-type?)))

(define rtype?
  (or/c TYPE? application?))

(define type?
  (or/c pi-type? rtype?))

(define tele?
  (listof scope?))

(define spine?
  (listof lambda-op?))

(define/contract
  (ctx-set ctx x ty)
  (-> ctx? free-name? pi-type? ctx?)
  (dict-set ctx x ty))

(define/contract
  (ctx-ref ctx x)
  (-> ctx? free-name? pi-type?)
  (dict-ref ctx x))

(define/contract
  (chk-ctx ctx tele)
  (-> ctx? tele? (cons/c ctx? (listof free-name?)))
  (define (aux ctx xs tele)
    (match tele
      ['() (cons ctx xs)]
      [(cons sc tele)
       (let* ([x (fresh)]
              [ty (inst sc xs)]
              [ctx (ctx-set ctx x ty)]
              [xs (snoc xs x)])
         (chk-type ctx ty)
         (aux ctx xs tele))]))
  (aux ctx '() tele))

(define/contract
  (chk-type ctx ty)
  (-> ctx? type? any/c)
  (match ty
    [(pi-type tele cod)
     (match (chk-ctx ctx tele)
       [(cons ctx xs)
        (chk-rtype ctx (inst cod xs))])]
    [rty (chk-rtype ctx rty)]))

(define/contract
  (chk-rtype ctx rty)
  (-> ctx? rtype? any/c)
  (match rty
    [(TYPE) 'ok]
    [application?
     (match (inf-rtm ctx rty)
       [(TYPE) 'ok])]))

(define/contract
  (chk-spine ctx tele spine)
  (-> ctx? tele? spine? any/c)
  (define (aux ctx env tele spine)
    (match* (tele spine)
      [('() '()) 'ok]
      [((cons sc tele) (cons ntm spine))
       (chk-ntm ctx ntm (inst sc env))
       (aux ctx (snoc env ntm) tele spine)]))
  (aux ctx '() tele spine))

(define/contract
  (chk-ntm ctx ntm ty)
  (-> ctx? lambda-op? pi-type? any/c)
  (match* (ntm ty)
    [((lambda-op sc) (pi-type tele cod))
     (match (chk-ctx ctx tele)
       [(cons ctx xs)
        (chk-rtm ctx (inst sc xs) (inst cod xs))])]))

(define/contract
  (inf-rtm ctx rtm)
  (-> ctx? application? rtype?)
  (match rtm
    [(application x spine)
     (match (ctx-ref ctx x)
       [(pi-type tele cod)
        (chk-spine ctx tele spine)
        (inst cod spine)])]))

(define/contract
  (chk-rtm ctx rtm rty)
  (-> ctx? application? rtype? any/c)
  (if (equal? (inf-rtm ctx rtm) rty)
      'ok
      (error "Type mismatch")))

(module+ test
  (let ([x (fresh "hello")])
    (check-equal?
     (Π (a x) (b ($ a)) ($ b))
     (Π (b x) (c ($ b)) ($ c))))

  (check-equal?
   (lam (n m) n)
   (lam (a b) a))

  ; TODO: pattern macros should get automatically generated!
  (define-for-syntax nat-expander
    (lambda (stx)
      (syntax-parse stx
        [(_)
         (syntax/loc stx ($ (free-name 'NAT "NAT")))])))

  (define-for-syntax ze-expander
    (lambda (stx)
      (syntax-parse stx
        [(_)
         (syntax/loc stx ($ (free-name 'ZE "ZE")))])))

  (define-for-syntax su-expander
    (lambda (stx)
      (syntax-parse stx
        [(_ e:expr)
         (syntax/loc stx ($ (free-name 'SU "SU") (lam () e)))])))

  (define-for-syntax ifze-expander
    (lambda (stx)
      (syntax-parse stx
        [(_ n:expr z:expr (x:id) s:expr)
         (syntax/loc stx
           ($ (free-name 'IFZE "IFZE") (lam () n) (lam () z) (lam (x) s)))])))

  (define-match-expander nat nat-expander nat-expander)
  (define-match-expander ze ze-expander ze-expander)
  (define-match-expander su su-expander su-expander)
  (define-match-expander ifze ifze-expander ifze-expander)

  ; we should automatically generate a pattern like
  ;    (ifze n z (x) s)
  ; for the operator IFZE

  ; an example signature. we should add macros to make it more tolerable
  ; to write and read such signatures.
  (define num-sig
    (signature
     (NAT (Π (TYPE)))
     (ZE (Π (nat)))
     (SU (Π (_ (Π (nat))) (nat)))
     (IFZE (Π (n (Π (nat))) (z (Π (nat))) (s (Π (x (Π (nat))) (nat))) (nat)))))

  (check-equal?
   (inf-rtm num-sig (ifze (su (su (ze))) (ze) (x) ($ x)))
   (nat))

  ;; deep matching on terms with binding! wow!
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
