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
 PI LAM APP TYPE
 Π lam
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


(struct PI (domain codomain)
  #:methods gen:custom-write
  ((define (write-proc pi port mode)
     (match-define (PI tl sc) pi)
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
     (match-define (PI tl sc) pi)
     (match-define (binder abs-tl _) bindings/telescope)
     (match-define (binder abs-sc _) (bindings-accessor sc))
     (PI (abs-tl tl frees i) (abs-sc sc frees i)))
   (λ (pi i new-exprs)
     (match-define (PI tl sc) pi)
     (match-define (binder _ inst-tl) bindings/telescope)
     (match-define (binder _ inst-sc) (bindings-accessor sc))
     (PI (inst-tl tl i new-exprs) (inst-sc sc i new-exprs))))

  #:methods gen:equal+hash
  ((define (equal-proc pi1 pi2 rec-equal?)
     (and
      (rec-equal? (PI-domain pi1) (PI-domain pi2))
      (rec-equal? (PI-codomain pi1) (PI-codomain pi2))))
   (define (hash-proc pi rec-hash)
     (fxxor
      (rec-hash (PI-domain pi))
      (rec-hash (PI-codomain pi))))
   (define (hash2-proc pi rec-hash2)
     (fxxor
      (rec-hash2 (PI-domain pi))
      (rec-hash2 (PI-codomain pi))))))

(struct LAM (scope)
  #:transparent ;; should it be transparent? Not sure. - jms
  #:methods gen:custom-write
  ((define (write-proc lam port mode)
     (match-define (LAM sc) lam)
     (define temps (fresh-print-names (scope-valence sc)))
     (define binder
       (string-join (for/list ([x temps]) (format "~a" x)) ", "))
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port "[~a]~a" binder (scope-body sc)))))

  #:property prop:bindings
  (binder
   (λ (lam frees i)
     (match-define (LAM sc) lam)
     (match-define (binder abs _) (bindings-accessor sc))
     (LAM (abs sc frees i)))
   (λ (lam i new-exprs)
     (match-define (LAM sc) lam)
     (match-define (binder _ inst) (bindings-accessor sc))
     (LAM (inst sc i new-exprs)))))


;; the TYPE type
(struct TYPE ()
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ty port mode)
     (fprintf port "TYPE")))
  #:property prop:bindings
  (binder
   (λ (ty frees i) ty)
   (λ (ty i new-exprs) ty)))

(struct APP (var spine)
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ap port mode)
     (match-define (APP x sp) ap)
     (define spine (string-join (for/list ([x sp]) (format "~a" x))))
     (fprintf port "~a[~a]" x spine)))

  #:property prop:bindings
  (binder
   (λ (ap frees i)
     (match-define (APP var spine) ap)
     (match-define (binder abs-var _) (bindings-accessor var))
     (define (go arg)
       (match-define (binder abs _) (bindings-accessor arg))
       (abs arg frees i))
     (APP (abs-var var frees i) (map go spine)))
   (λ (ap i new-exprs)
     (match-define (APP var spine) ap)
     (match-define (binder _ inst-var) (bindings-accessor var))
     (define (go-arg arg)
       (match-define (binder _ inst-arg) (bindings-accessor arg))
       (inst-arg arg i new-exprs))
     (define new-spine (map go-arg spine))
     (match (inst-var var i new-exprs)
       [(bound-name ix) (APP (bound-name ix) new-spine)]
       [(free-name sym hint) (APP (free-name sym hint) new-spine)]
       [(LAM sc)
        (define body (scope-body sc))
        (match-let ([(binder _ inst-body) (bindings-accessor body)])
          (inst-body body i new-spine))]))))



(define-for-syntax sig-expander
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ty:expr) ...)
       (with-syntax ([(x-var ...) (syntax->datum #'(x ...))])
         (syntax/loc stx
           (list (cons (free-name 'x (symbol->string 'x)) ty) ...)))])))

(define-match-expander signature sig-expander sig-expander)

; TODO: have this generate match expanders as it goes!
(define-syntax-rule (define-signature sig-name (x ty) ...)
  (define sig-name
    (signature (x ty) ...)))

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

(define-for-syntax Π-expander
  (λ (stx)
    (syntax-parse stx
      [(_ ((x:id e:expr) ...) cod:expr)
       (syntax/loc stx (PI (telescope (x e) ...) (in-scope (x ...) cod)))])))

(define-match-expander Π Π-expander Π-expander)

(define-for-syntax lam-expander
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (syntax/loc stx (LAM (in-scope (x ...) body)))])))

(define-match-expander lam lam-expander lam-expander)

(define-for-syntax $-expander
  (λ (stx)
    (syntax-parse stx
      [(_ x:expr e:expr ...)
       (syntax/loc stx (APP x (list e ...)))])))

(define-match-expander $ $-expander $-expander)


; a signature/context is an association list

(define (snoc xs x)
  (append xs (list x)))

(define ctx?
  (listof (cons/c free-name? PI?)))

(define rtype?
  (or/c TYPE? APP?))

(define type?
  (or/c PI? rtype?))

(define tele?
  (listof scope?))

(define spine?
  (listof LAM?))

(define/contract
  (ctx-set ctx x ty)
  (-> ctx? free-name? PI? ctx?)
  (dict-set ctx x ty))

(define/contract
  (ctx-ref ctx x)
  (-> ctx? free-name? PI?)
  (dict-ref ctx x))

(define/contract
  (chk-tele ctx tele)
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

(define/contract
  (wf-tele? ctx)
  (-> ctx? (-> tele? boolean?))
  (λ (tele)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-tele ctx tele)
      #t)))


(define/contract
  (wf-rtype? ctx)
  (-> ctx? (-> rtype? boolean?))
  (λ (rty)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-rtype ctx rty)
      #t)))

(define/contract
  (chk-type ctx ty)
  (-> ctx? type? any/c)
  (match ty
    [(PI tele cod)
     (match (chk-tele ctx tele)
       [(cons ctx xs)
        (chk-rtype ctx (instantiate cod xs))])]))


(define/contract
  (wf-type? ctx)
  (-> ctx? (-> type? boolean?))
  (λ (ty)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-type ctx ty)
      #t)))

(define/contract
  (chk-rtype ctx rty)
  (-> ctx? rtype? any/c)
  (match rty
    [(TYPE) #t]
    [APP?
     (match (inf-rtm ctx rty)
       [(TYPE) '#t])]))

(define/contract
  (chk-spine ctx tele spine)
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


(define/contract
  (wf-spine? ctx tele)
  (->i ((ctx ctx?)
        (tele (ctx) (wf-tele? ctx)))
       (result (-> spine? boolean?)))
  (λ (spine)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-spine ctx spine tele)
      #t)))

(define/contract
  (chk-ntm ctx ntm ty)
  (->i ((ctx ctx?)
        (ntm LAM?)
        (ty (ctx ntm) (wf-type? ctx)))
       (result any/c))
  (match* (ntm ty)
    [((LAM sc) (PI tele cod))
     (match (chk-tele ctx tele)
       [(cons ctx xs)
        (chk-rtm ctx (instantiate sc xs) (instantiate cod xs))])]))


(define/contract
  (wf-ntm? ctx ty)
  (->i ((ctx ctx?)
        (ty (ctx) (wf-type? ctx)))
       (result (-> LAM? boolean?)))
  (λ (ntm)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-ntm ctx ntm ty)
      #t)))

(define/contract
  (inf-rtm ctx rtm)
  (->i ((ctx ctx?)
        (rtm APP?))
       (result (ctx rtm) (wf-rtype? ctx)))
  (match rtm
    [(APP x spine)
     (match (ctx-ref ctx x)
       [(PI tele cod)
        (chk-spine ctx tele spine)
        (instantiate cod spine)])]))

(define/contract
  (chk-rtm ctx rtm rty)
  (-> ctx? APP? rtype? any/c)
  (if (equal? (inf-rtm ctx rtm) rty)
      #t
      (error "Type mismatch")))

(define/contract
  (wf-rtm? ctx rty)
  (->i ((ctx ctx?)
        (rty (ctx) (wf-rtype? ctx)))
       (result (-> APP? boolean?)))
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
   (lam (n m) n)
   (lam (a b) a))

  ; TODO: pattern macros should get automatically generated!
  (define-for-syntax nat-expander
    (λ (stx)
      (syntax-parse stx
        [(_)
         (syntax/loc stx ($ (free-name 'NAT "NAT")))])))

  (define-for-syntax ze-expander
    (λ (stx)
      (syntax-parse stx
        [(_)
         (syntax/loc stx ($ (free-name 'ZE "ZE")))])))

  (define-for-syntax su-expander
    (λ (stx)
      (syntax-parse stx
        [(_ e:expr)
         (syntax/loc stx ($ (free-name 'SU "SU") (lam () e)))])))

  (define-for-syntax ifze-expander
    (λ (stx)
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
  (define-signature num-sig
    (NAT (Π () (TYPE)))
    (ZE (Π () (nat)))
    (SU (Π ((_ (Π () (nat)))) (nat)))
    (IFZE
     (Π
      ((n (Π () (nat)))
       (z (Π () (nat)))
       (s (Π ((x (Π () (nat)))) (nat))))
      (nat))))

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
