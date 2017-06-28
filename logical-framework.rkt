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
 TYPE => Λ $
 =>? Λ? $? rtype? ctx?
 define-signature telescope
 make-wf-=> =>-domain =>-codomain
 make-wf-Λ
 make-wf-$
 as-classifier
 ctx-set ctx-ref ctx-map
 ctx->tele tele->ctx
 chk-type
 chk-rtype
 chk-tele
 chk-ntm
 chk-rtm
 chk-spine
 inf-rtm
 
 ok-rtype?
 ok-type?
 ok-tele?
 ok-spine?
 ok-ntm?
 ok-rtm?)

(module+ test
  (require rackunit))


(struct => (domain codomain wf)
  #:omit-define-syntaxes
  #:extra-constructor-name make-=>
  #:methods gen:custom-write
  ((define (write-proc pi port mode)
     (define tl (=>-domain pi))
     (define sc (=>-codomain pi))
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
     (define tl (=>-domain pi))
     (define sc (=>-codomain pi))
     (match-define (binder abs-tl _) bindings/telescope)
     (match-define (binder abs-sc _) (bindings-accessor sc))
     (make-=> (abs-tl tl frees i) (abs-sc sc frees i) (=>-wf pi)))
   (λ (pi i new-exprs)
     (define tl (=>-domain pi))
     (define sc (=>-codomain pi))
     (match-define (binder _ inst-tl) bindings/telescope)
     (match-define (binder _ inst-sc) (bindings-accessor sc))
     (make-=> (inst-tl tl i new-exprs) (inst-sc sc i new-exprs) (=>-wf pi))))

  #:methods gen:equal+hash
  ((define (equal-proc pi1 pi2 rec-equal?)
     (and
      (rec-equal? (=>-domain pi1) (=>-domain pi2))
      (rec-equal? (=>-codomain pi1) (=>-codomain pi2))))
   (define (hash-proc pi rec-hash)
     (fxxor
      (rec-hash (=>-domain pi))
      (rec-hash (=>-codomain pi))))
   (define (hash2-proc pi rec-hash2)
     (fxxor
      (rec-hash2 (=>-domain pi))
      (rec-hash2 (=>-codomain pi))))))

(define-match-expander =>
  (λ (stx)
    (syntax-parse stx
      [(_ ((x:id e:expr) ...) cod:expr)
       (syntax/loc stx
         (? =>? (and (app =>-domain (telescope (x e) ...))
                    (app =>-codomain (in-scope (x ...) cod)))))]))
  (λ (stx)
    (syntax-parse stx
      [(_ ((x:id e:expr) ...) cod:expr)
       (syntax/loc stx
         (make-wf-=> (telescope (x e) ...) (in-scope (x ...) cod)))])))

(struct Λ (scope wf)
  #:omit-define-syntaxes
  #:extra-constructor-name make-Λ
  #:methods gen:custom-write
  ((define (write-proc e port mode)
     (define sc (Λ-scope e))
     (define temps (fresh-print-names (scope-valence sc)))
     (define binder
       (string-join (for/list ([x temps]) (format "~a" x)) " "))
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port "(Λ (~a) ~a)" binder (scope-body sc)))))

  #:property prop:bindings
  (binder
   (λ (e frees i)
     (define sc (Λ-scope e))
     (match-define (binder abs _) (bindings-accessor sc))
     (make-Λ (abs sc frees i) (Λ-wf e)))
   (λ (e i new-exprs)
     (define sc (Λ-scope e))
     (match-define (binder _ inst) (bindings-accessor sc))
     (make-Λ (inst sc i new-exprs) (Λ-wf e))))


  #:methods gen:equal+hash
  ((define (equal-proc lam1 lam2 rec-equal?)
     (rec-equal? (Λ-scope lam1) (Λ-scope lam2)))
   (define (hash-proc lam rec-hash)
     (rec-hash (Λ-scope lam)))
   (define (hash2-proc lam rec-hash2)
     (rec-hash2 (Λ-scope lam)))))

(define-match-expander Λ
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (syntax/loc stx
         (? Λ? (app Λ-scope (in-scope (x ...) body))))]))
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (syntax/loc stx
         (make-wf-Λ (in-scope (x ...) (as-atomic-term body))))])))

(struct TYPE ()
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ty port mode)
     (fprintf port "(TYPE)")))
  #:property prop:bindings
  (binder
   (λ (ty frees i) ty)
   (λ (ty i new-exprs) ty)))

(struct $ (var spine wf)
  #:omit-define-syntaxes
  #:extra-constructor-name make-$
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ap port mode)
     (define x ($-var ap))
     (define sp ($-spine ap))
     (define spine (string-join (for/list ([x sp]) (format "~a" x)) " "))
     (fprintf port "($ ~a ~a)" x spine)))

  #:property prop:bindings
  (binder
   (λ (ap frees i)
     (define var ($-var ap))
     (define spine ($-spine ap))
     (match-define (binder abs-var _) (bindings-accessor var))
     (define (go arg)
       (match-define (binder abs _) (bindings-accessor arg))
       (abs arg frees i))
     (make-$ (abs-var var frees i) (map go spine) ($-wf ap)))
   (λ (ap i new-exprs)
     (define var ($-var ap))
     (define spine ($-spine ap))
     (match-define (binder _ inst-var) (bindings-accessor var))
     (define (go-arg arg)
       (match-define (binder _ inst-arg) (bindings-accessor arg))
       (inst-arg arg i new-exprs))
     (define new-spine (map go-arg spine))
     (match (inst-var var i new-exprs)
       [(bound-name ix) (make-$ (bound-name ix) new-spine ($-wf ap))]
       [(free-name sym hint) (make-$ (free-name sym hint) new-spine ($-wf ap))]
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
         (as-atomic-term (make-wf-$ x (list e ...))))])))

(define (under-scope f sc)
  (match-define (cons vars body) (auto-instantiate sc))
  (abstract vars (f body)))

(define (make-wf-=> tele cod)
  (make-=> (as-telescope tele) (under-scope as-base-classifier cod) #t))

(define (make-wf-Λ sc)
  (make-Λ (under-scope as-atomic-term sc) #t))

(define (make-wf-$ x sp)
  (make-$ x (as-spine sp) #t))


(define (as-classifier tm)
  (match tm
    [(? =>? (and (app =>-wf #f) (app =>-domain tele) (app =>-codomain cod)))
     (make-wf-=> tele cod)]
    [(? =>? _) tm]
    [_ (=> () (as-base-classifier tm))]))

(define (as-base-classifier tm)
  (match tm
    [(TYPE) (TYPE)]
    [_ (as-atomic-term tm)]))

(define (as-telescope tele)
  (for/list ([sc (in-list tele)])
    (under-scope as-classifier sc)))

(define (as-atomic-term tm)
  (match tm
    [(? $? (and (app $-wf #f) (app $-var x) (app $-spine sp)))
     (if (free-name? x)
         (make-wf-$ x sp)
         (error "Crappy term!!"))]
    [(? $? _) tm]
    [(? free-name?)
     ($ tm)]
    [_ (error (format "Crappy term!!! ~a" tm))]))

(define (as-spine sp)
  (map as-term sp))

(define (as-term tm)
  (match tm
    [(? Λ? (and (app Λ-wf #f) (app Λ-scope sc))) (make-wf-Λ sc)]
    [(? Λ? _) tm]
    [_ (Λ () (as-atomic-term tm))]))


(define (unwrap-nullary-binder tm)
  (match tm
    [(=> () tm) tm]
    [(Λ () tm) tm]
    [_ tm]))

(module+ test
  (check-true
   (match (as-term (fresh))
     [(Λ () ($ (? free-name?))) #t]
     [_ #f]))

  (check-equal?
   (as-classifier (=> ((x (TYPE))) (TYPE)))
   (=> ((x (=> () (TYPE)))) (TYPE)))

  (let ([x (fresh)] [y (fresh)])
    (check-equal?
     (as-classifier ($ x y))
     (=> () ($ x (Λ () ($ y)))))))

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
    #:literals (=>)
    [(_ (x:id (=> () e)))
     (syntax/loc stx
       (x))]
    [(_ (x:id (=> (y1 y ...) e)) elem ...)
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
    #:literals (=>)
    ;; TODO: Add another pattern here to add implicit Pi when not used directly?
    (pattern
     (=> () result)
     #:attr (arg 1) '())
    (pattern
     (=> ((arg:id type) ...) result))))



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
       #'(begin
           (define-for-syntax (help-pattern-expander stx)
             (syntax-parse stx
               [(_ lhs ...)
                (with-syntax ([name-str (symbol->string (syntax->datum #'name))])
                  (syntax/loc stx
                    (app unwrap-nullary-binder
                         ($ (free-name 'name name-str)
                            rhs
                            ...))))]))
           (define-for-syntax (help-constructor-expander stx)
             (syntax-parse stx
               [(_ lhs ...)
                (with-syntax ([name-str (symbol->string (syntax->datum #'name))])
                  (syntax/loc stx
                    ($ (free-name 'name name-str)
                       rhs
                       ...)))]))
           (define-match-expander name help-pattern-expander help-constructor-expander)))]))

(define-syntax (define-signature stx)
  (syntax-parse stx
    [(_ sig-name c:signature-elem ...)
     #'(begin
         (define sig-name
           (signature (c.name (=> ((c.arg c.type) ...) c.result)) ...))
         (define-signature-helper c.name ((c.arg c.type) ...)) ...)]))

(define (snoc xs x)
  (append xs (list x)))

(define ctx?
  (listof (cons/c free-name? any/c)))

(define rtype?
  (or/c TYPE? $?))

(define type? =>?)

(define tele?
  (listof scope?))

(define spine?
  (listof Λ?))

(define/contract (ctx->tele ctx)
  (-> ctx? tele?)
  (define (aux xs ctx)
    (match ctx
      ['() '()]
      [(cons (cons x ty) ctx)
       (cons (abstract xs ty) (aux (snoc xs x) ctx))]))
  (aux '() ctx))

;; Need to check if this is right
(define (tele->ctx names tele)
  (define (aux xs tele ctx)
    (match* (xs tele)
      [('() '()) ctx]
      [((cons x xs) (cons sc tele))
       (aux xs tele (ctx-set ctx x (instantiate sc (map car ctx))))]))
  (aux names tele '()))

(define/contract (chk-ctx? ctx)
  (-> ctx? any/c)
  (chk-tele '() (ctx->tele ctx))
  '())

(define/contract (wf-ctx? ctx)
  (-> ctx? boolean?)
  ((ok-tele? '()) (ctx->tele ctx)))


(define/contract (ctx-set ctx x ty)
  (-> ctx? free-name? any/c ctx?)
  (dict-set ctx x ty))

(define/contract (ctx-ref ctx x)
  (-> ctx? free-name? any/c)
  (dict-ref ctx x))

(define (cell-map f)
  (λ (cell)
    (cons
     (car cell)
     (f (cdr cell)))))

(define (ctx-map f Γ)
  (map (cell-map f) Γ))

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

(define/contract (ok-tele? ctx)
  (-> ctx? (-> tele? boolean?))
  (λ (tele)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-tele ctx tele)
      #t)))


(define/contract (ok-rtype? ctx)
  (-> ctx? (-> rtype? boolean?))
  (λ (rty)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-rtype ctx rty)
      #t)))

(define/contract (chk-type ctx ty)
  (-> ctx? type? any/c)
  (match ty
    [(? =>? (and (app =>-domain tele) (app =>-codomain cod)))
     (match (chk-tele ctx tele)
       [(cons ctx xs)
        (chk-rtype ctx (instantiate cod xs))])]))


(define/contract (ok-type? ctx)
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
        (tele (ctx) (ok-tele? ctx))
        (spine spine?))
       (result any/c))
  (define (aux ctx env tele spine)
    (match* (tele spine)
      [('() '()) #t]
      [((cons sc tele) (cons ntm spine))
       (chk-ntm ctx ntm (instantiate sc env))
       (aux ctx (snoc env ntm) tele spine)]))
  (aux ctx '() tele spine))


(define/contract (ok-spine? ctx tele)
  (->i ((ctx ctx?)
        (tele (ctx) (ok-tele? ctx)))
       (result (-> spine? boolean?)))
  (λ (spine)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-spine ctx spine tele)
      #t)))

(define/contract (chk-ntm ctx ntm ty)
  (->i ((ctx ctx?)
        (ntm Λ?)
        (ty (ctx ntm) (ok-type? ctx)))
       (result any/c))
  (match* (ntm ty)
    [((? Λ? (app Λ-scope sc)) (? =>? (and (app =>-domain tele) (app =>-codomain cod))))
     (match (chk-tele ctx tele)
       [(cons ctx xs)
        (chk-rtm ctx (instantiate sc xs) (instantiate cod xs))])]))


(define/contract (ok-ntm? ctx ty)
  (->i ((ctx ctx?)
        (ty (ctx) (ok-type? ctx)))
       (result (-> Λ? boolean?)))
  (λ (ntm)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-ntm ctx ntm ty)
      #t)))

(define/contract (inf-rtm ctx rtm)
  (->i ((ctx ctx?)
        (rtm $?))
       (result (ctx rtm) (ok-rtype? ctx)))
  (match rtm
    [(? $? (and (app $-var x) (app $-spine spine)))
     (match (ctx-ref ctx x)
       [(? =>? (and (app =>-domain tele) (app =>-codomain cod)))
        (chk-spine ctx tele spine)
        (instantiate cod spine)])]))

(define/contract (chk-rtm ctx rtm rty)
  (-> ctx? $? rtype? any/c)
  (if (equal? (inf-rtm ctx rtm) rty)
      #t
      (error "Type mismatch")))

(define/contract (ok-rtm? ctx rty)
  (->i ((ctx ctx?)
        (rty (ctx) (ok-rtype? ctx)))
       (result (-> $? boolean?)))
  (λ (rtm)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (chk-rtm ctx rtm rty)
      #t)))


(module+ test
  (=> ((a (fresh)) (b a)) b)
  
  (let ([x (fresh "hello")])
    (check-equal?
     (=> ((a x) (b a)) b)
     (=> ((b x) (c ($ b))) ($ c))))

  (check-equal?
   (Λ (n m) n)
   (Λ (a b) a))

  (define-signature num-sig
    (nat () (TYPE))
    (ze () (nat))
    (su ((x (=> () (nat))))
        (nat))
    (ifze ((n (=> () (nat)))
           (z (=> () (nat)))
           (s (=> ((x (nat))) (nat))))
          (nat)))

  (chk-ctx? num-sig)

  ; An example of structural recursion over terms,
  ; using the auto-generated patterns
  (define (printer rtm)
    (match rtm
      [(nat) "nat"]
      [(ze) "ze"]
      [(su e) (format "su(~a)" (printer e))]
      [(ifze n z (x) s)
       (format
        "ifze(~a; ~a; ~a.~a)"
        (printer n)
        (printer z)
        (free-name-hint x)
        (printer s))]
      [($ x) (free-name-hint x)]))

  (check-equal?
   (inf-rtm num-sig (ifze (su (su (ze))) (ze) (x) x))
   (nat))

  (check-equal?
   (printer
    (ifze (su (su (ze))) (ze) (x) (su x)))
   "ifze(su(su(ze)); ze; x.su(x))")

  (match (ifze (su (su (ze))) (ze) (x) (su x))
    [(ifze (su (su n)) z (x) s)
     (check-equal? s (su x))])

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
