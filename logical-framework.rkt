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
 SORT arity bind plug
 arity? bind? plug? sort? ctx? tele?
 define-signature telescope
 make-arity arity-domain arity-codomain
 make-bind
 make-plug
 plug-var plug-spine
 as-arity
 as-atomic-term
 as-term

 subst

 ctx-set ctx-ref ctx-map
 ctx->telescope telescope->ctx

 check-arity
 check-sort
 check-telescope
 check-term
 check-atomic-term
 check-spine
 infer-atomic-term

 ok-sort?
 ok-arity?
 ok-telescope?
 ok-spine?
 ok-term?
 ok-atomic-term?

 under-scope)

(module+ test
  (require rackunit))


(define ctx?
  (listof (cons/c free-name? any/c)))


(define tele?
  (listof scope?))



(struct arity (domain codomain)
  #:omit-define-syntaxes
  #:extra-constructor-name raw-make-arity
  #:methods gen:custom-write
  ((define (write-proc pi port mode)
     (define tl (arity-domain pi))
     (define sc (arity-codomain pi))
     (match-define (scope vl body) sc)
     (define temps (fresh-print-names vl))
     (fprintf port "(arity ")
     (write-proc/telescope tl port mode)
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port " ~a)" body))))

  #:property prop:bindings
  (bindings-support
   (λ (pi frees i)
     (define tl (arity-domain pi))
     (define sc (arity-codomain pi))
     (match-define (bindings-support abs-tl _) bindings/telescope)
     (match-define (bindings-support abs-sc _) (bindings-accessor sc))
     (raw-make-arity (abs-tl tl frees i) (abs-sc sc frees i)))
   (λ (pi i new-exprs)
     (define tl (arity-domain pi))
     (define sc (arity-codomain pi))
     (match-define (bindings-support _ inst-tl) bindings/telescope)
     (match-define (bindings-support _ inst-sc) (bindings-accessor sc))
     (raw-make-arity (inst-tl tl i new-exprs) (inst-sc sc i new-exprs))))

  #:methods gen:equal+hash
  ((define (equal-proc pi1 pi2 rec-equal?)
     (and
      (rec-equal? (arity-domain pi1) (arity-domain pi2))
      (rec-equal? (arity-codomain pi1) (arity-codomain pi2))))
   (define (hash-proc pi rec-hash)
     (fxxor
      (rec-hash (arity-domain pi))
      (rec-hash (arity-codomain pi))))
   (define (hash2-proc pi rec-hash2)
     (fxxor
      (rec-hash2 (arity-domain pi))
      (rec-hash2 (arity-codomain pi))))))

(define-match-expander arity
  (λ (stx)
    (syntax-parse stx
      [(_ ((x:id e:expr) ...) cod:expr)
       (syntax/loc stx
         (? arity? (and (app arity-domain (telescope (x e) ...))
                        (app arity-codomain (in-scope (x ...) cod)))))]))
  (λ (stx)
    (syntax-parse stx
      [(_ ((x:id e:expr) ...) cod:expr)
       (syntax/loc stx
         (make-arity (telescope (x e) ...) (in-scope (x ...) cod)))])))

(struct bind (scope)
  #:omit-define-syntaxes
  #:extra-constructor-name raw-make-bind
  #:methods gen:custom-write
  ((define (write-proc e port mode)
     (define sc (bind-scope e))
     (define temps (fresh-print-names (scope-valence sc)))
     (define binder
       (string-join (for/list ([x temps]) (format "~a" x)) " "))
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port "(bind (~a) ~a)" binder (scope-body sc)))))

  #:property prop:bindings
  (bindings-support
   (λ (e frees i)
     (define sc (bind-scope e))
     (match-define (bindings-support abs _) (bindings-accessor sc))
     (raw-make-bind (abs sc frees i)))
   (λ (e i new-exprs)
     (define sc (bind-scope e))
     (match-define (bindings-support _ inst) (bindings-accessor sc))
     (raw-make-bind (inst sc i new-exprs))))


  #:methods gen:equal+hash
  ((define (equal-proc lam1 lam2 rec-equal?)
     (rec-equal? (bind-scope lam1) (bind-scope lam2)))
   (define (hash-proc lam rec-hash)
     (rec-hash (bind-scope lam)))
   (define (hash2-proc lam rec-hash2)
     (rec-hash2 (bind-scope lam)))))

(define-match-expander bind
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (syntax/loc stx
         (? bind? (app bind-scope (in-scope (x ...) body))))]))
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (syntax/loc stx
         (make-bind (in-scope (x ...) body)))])))

(struct SORT ()
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ty port mode)
     (fprintf port "(SORT)")))
  #:property prop:bindings
  (bindings-support
   (λ (ty frees i) ty)
   (λ (ty i new-exprs) ty)))

(struct plug (var spine)
  #:omit-define-syntaxes
  #:extra-constructor-name raw-make-plug
  #:transparent
  #:methods gen:custom-write
  ((define (write-proc ap port mode)
     (define x (plug-var ap))
     (define sp (plug-spine ap))
     (define spine (string-join (for/list ([x sp]) (format "~a" x)) " "))
     (match sp
       ['() (fprintf port "(plug ~a)" x)]
       [_ (fprintf port "(plug ~a ~a)" x spine)])))

  #:property prop:bindings
  (bindings-support
   (λ (ap frees i)
     (define var (plug-var ap))
     (define spine (plug-spine ap))
     (match-define (bindings-support abs-var _) (bindings-accessor var))
     (raw-make-plug
      (abs-var var frees i)
      (for/list ([arg spine])
        (match-define (bindings-support abs _) (bindings-accessor arg))
        (abs arg frees i))))
   (λ (ap i new-exprs)
     (define var (plug-var ap))
     (define spine (plug-spine ap))
     (match-define (bindings-support _ inst-var) (bindings-accessor var))
     (define new-spine
       (for/list ([arg spine])
         (match-define (bindings-support _ inst-arg) (bindings-accessor arg))
         (inst-arg arg i new-exprs)))
     (match (inst-var var i new-exprs)
       [(bound-name ix) (raw-make-plug (bound-name ix) new-spine)]
       [(free-name sym hint) (raw-make-plug (free-name sym hint) new-spine)]
       [(? bind? (app bind-scope sc))
        (define body (scope-body sc))
        (match-let ([(bindings-support _ inst-body) (bindings-accessor body)])
          (inst-body body i new-spine))]))))

(define-match-expander plug
  (λ (stx)
    (syntax-parse stx
      [(_ x e ...)
       (syntax/loc stx
         (? plug?
            (and (app plug-var x)
                 (app plug-spine (list e ...)))))]))
  (λ (stx)
    (syntax-parse stx
      [(_ x e ...)
       (syntax/loc stx
         (as-atomic-term (make-plug x (list e ...))))])))

(define (sort? e)
  (or (SORT? e) (plug? e)))

(define spine?
  (listof bind?))

(define/contract (under-scope f sc)
  (-> any/c scope? scope?)
  (match-define (cons vars body) (auto-instantiate sc))
  (abstract vars (f body)))

(define/contract (make-arity tele cod)
  (-> tele? scope? arity?)
  (raw-make-arity (as-telescope tele) (under-scope as-sort cod)))

(define/contract (make-bind sc)
  (-> scope? bind?)
  (raw-make-bind (under-scope as-atomic-term sc)))

(define/contract (make-plug x sp)
  (-> free-name? (listof any/c) plug?)
  (raw-make-plug x (as-spine sp)))

(define (as-arity tm)
  (match tm
    [(? arity? _) tm]
    [_ (arity () (as-sort tm))]))

(define (as-sort tm)
  (match tm
    [(SORT) (SORT)]
    [_ (as-atomic-term tm)]))

(define (as-telescope tele)
  (for/list ([sc (in-list tele)])
    (under-scope as-arity sc)))

(define (as-atomic-term tm)
  (match tm
    [(? plug? (app plug-var x))
     (if (free-name? x)
         tm
         (error "Crappy term!!"))]
    [(? free-name?)
     (plug tm)]
    [_ (error (format "Crappy term!!! ~a" tm))]))

(define (as-spine sp)
  (map as-term sp))

(define (as-term tm)
  (match tm
    [(? bind? _) tm]
    [_ (bind () (as-atomic-term tm))]))


(define (unwrap-nullary-binder tm)
  (match tm
    [(arity () tm) tm]
    [(bind () tm) tm]
    [_ tm]))

(module+ test
  (check-true
   (match (as-term (fresh))
     [(bind () (plug (? free-name?))) #t]
     [_ #f]))

  (check-equal?
   (as-arity (arity ((x (SORT))) (SORT)))
   (arity ((x (arity () (SORT)))) (SORT)))

  (let ([x (fresh)] [y (fresh)])
    (check-equal?
     (as-arity (plug x y))
     (arity () (plug x (bind () (plug y)))))))

(define-for-syntax sig-expander
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ty:expr) ...)
       (syntax/loc stx
         (list (cons (free-name 'x (symbol->string 'x)) ty) ...))])))

(define-match-expander signature sig-expander sig-expander)

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


(define-syntax (subst stx)
  (syntax-parse stx
    [(_ ([x:id (y:id ...) ex:expr] ...) e:expr)
     (syntax/loc stx
       (instantiate
           (abstract (list x ...) e)
         (list (bind (y ...) ex) ...)))]
    [(_ [x:id (y:id ...) ex:expr] e:expr)
     (syntax/loc stx
       (instantiate
           (abstract (list x) (bind (y ...) e))
         (list ex)))]))


; a signature/context is an association list

(begin-for-syntax
  (define-syntax-class signature-elem
    (pattern (name:id ((arg:id type:Pi) ...) result)))
  (define-syntax-class Pi
    #:literals (arity)
    ;; TODO: Add another pattern here to add implicit Pi when not used directly?
    (pattern
     (arity () result)
     #:attr (arg 1) '())
    (pattern
     (arity ((arg:id type) ...) result))))



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
                         #'(bind (y ...) x)]))])
       #'(begin
           (define-for-syntax (help-pattern-expander stx)
             (syntax-parse stx
               [(_ lhs ...)
                (with-syntax ([name-str (symbol->string (syntax->datum #'name))])
                  (syntax/loc stx
                    (app unwrap-nullary-binder
                         (plug (free-name 'name name-str)
                               rhs
                               ...))))]))
           (define-for-syntax (help-constructor-expander stx)
             (syntax-parse stx
               [(_ lhs ...)
                (with-syntax ([name-str (symbol->string (syntax->datum #'name))])
                  (syntax/loc stx
                    (plug (free-name 'name name-str)
                          rhs
                          ...)))]))
           (define-match-expander name help-pattern-expander help-constructor-expander)))]))

(define-syntax (define-signature stx)
  (syntax-parse stx
    [(_ sig-name c:signature-elem ...)
     #'(begin
         (define sig-name
           (signature (c.name (arity ((c.arg c.type) ...) c.result)) ...))
         (define-signature-helper c.name ((c.arg c.type) ...)) ...)]))

(define (snoc xs x)
  (append xs (list x)))


(define/contract (ctx->telescope ctx)
  (-> ctx? tele?)
  (define (aux xs ctx)
    (match ctx
      ['() '()]
      [(cons (cons x ty) ctx)
       (cons (abstract xs ty) (aux (snoc xs x) ctx))]))
  (aux '() ctx))

;; Need to check if this is right
(define (telescope->ctx names tele)
  (define (aux xs tele ctx)
    (match* (xs tele)
      [('() '()) (reverse ctx)]
      [((cons x xs) (cons sc tele))
       (aux xs tele (cons (cons  x (instantiate sc (map car ctx))) ctx))]))
  (aux names tele '()))

(define/contract (chk-ctx? ctx)
  (-> ctx? any/c)
  (check-telescope '() (ctx->telescope ctx))
  '())

(define/contract (wf-ctx? ctx)
  (-> ctx? boolean?)
  ((ok-telescope? '()) (ctx->telescope ctx)))

(define/contract (ctx-set ctx x ty)
  (-> ctx? free-name? any/c ctx?)
  (dict-set ctx x (as-arity ty)))

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

(define/contract (check-telescope ctx tele)
  (-> ctx? tele? (cons/c ctx? (listof free-name?)))
  (define (aux ctx xs tele)
    (match tele
      ['() (cons ctx xs)]
      [(cons sc tele)
       (let* ([x (fresh)]
              [ty (instantiate sc xs)]
              [ctx (dict-set ctx x ty)]
              [xs (snoc xs x)])
         (check-arity ctx ty)
         (aux ctx xs tele))]))
  (aux ctx '() tele))

(define/contract (ok-telescope? ctx)
  (-> ctx? (-> tele? boolean?))
  (λ (tele)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (check-telescope ctx tele)
      #t)))


(define/contract (ok-sort? ctx)
  (-> ctx? (-> sort? boolean?))
  (λ (rty)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (check-sort ctx rty)
      #t)))

(define/contract (check-arity ctx ty)
  (-> ctx? arity? any/c)
  (match ty
    [(? arity? (and (app arity-domain tele) (app arity-codomain cod)))
     (match (check-telescope ctx tele)
       [(cons ctx xs)
        (check-sort ctx (instantiate cod xs))])]))


(define/contract (ok-arity? ctx)
  (-> ctx? (-> arity? boolean?))
  (λ (ty)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (check-arity ctx ty)
      #t)))

(define/contract (check-sort ctx rty)
  (-> ctx? sort? any/c)
  (match rty
    [(SORT) #t]
    [APP?
     (match (infer-atomic-term ctx rty)
       [(SORT) '#t])]))

(define/contract (check-spine ctx tele spine)
  (->i ((ctx ctx?)
        (tele (ctx) (ok-telescope? ctx))
        (spine spine?))
       (result any/c))
  (define (aux ctx env tele spine)
    (match* (tele spine)
      [('() '()) #t]
      [((cons sc tele) (cons ntm spine))
       (check-term ctx ntm (instantiate sc env))
       (aux ctx (snoc env ntm) tele spine)]))
  (aux ctx '() tele spine))


(define/contract (ok-spine? ctx tele)
  (->i ((ctx ctx?)
        (tele (ctx) (ok-telescope? ctx)))
       (result (-> spine? boolean?)))
  (λ (spine)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (check-spine ctx spine tele)
      #t)))

(define/contract (check-term ctx ntm ty)
  (->i ((ctx ctx?)
        (ntm bind?)
        (ty (ctx ntm) (ok-arity? ctx)))
       (result any/c))
  (match* (ntm ty)
    [((? bind? (app bind-scope sc)) (? arity? (and (app arity-domain tele) (app arity-codomain cod))))
     (match (check-telescope ctx tele)
       [(cons ctx xs)
        (check-atomic-term ctx (instantiate sc xs) (instantiate cod xs))])]))


(define/contract (ok-term? ctx ty)
  (->i ((ctx ctx?)
        (ty (ctx) (ok-arity? ctx)))
       (result (-> bind? boolean?)))
  (λ (ntm)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (check-term ctx ntm ty)
      #t)))

(define/contract (infer-atomic-term ctx rtm)
  (->i ((ctx ctx?)
        (rtm plug?))
       (result (ctx rtm) (ok-sort? ctx)))
  (match rtm
    [(? plug? (and (app plug-var x) (app plug-spine spine)))
     (match (ctx-ref ctx x)
       [(? arity? (and (app arity-domain tele) (app arity-codomain cod)))
        (check-spine ctx tele spine)
        (instantiate cod spine)])]))

(define/contract (check-atomic-term ctx rtm rty)
  (-> ctx? plug? sort? any/c)
  (if (equal? (infer-atomic-term ctx rtm) rty)
      #t
      (error "Type mismatch")))

(define/contract (ok-atomic-term? ctx rty)
  (->i ((ctx ctx?)
        (rty (ctx) (ok-sort? ctx)))
       (result (-> plug? boolean?)))
  (λ (rtm)
    (with-handlers ([exn:fail? (λ (v) #f)])
      (check-atomic-term ctx rtm rty)
      #t)))


(module+ test
  (arity ((a (fresh)) (b a)) b)

  (let ([x (fresh "hello")])
    (check-equal?
     (arity ((a x) (b a)) b)
     (arity ((b x) (c (plug b))) (plug c))))

  (check-equal?
   (bind (n m) n)
   (bind (a b) a))

  (define-signature num-sig
    (nat () (SORT))
    (ze () (nat))
    (su ((x (arity () (nat))))
        (nat))
    (ifze ((n (arity () (nat)))
           (z (arity () (nat)))
           (s (arity ((x (nat))) (nat))))
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
      [(plug x) (free-name-hint x)]))

  (check-equal?
   (infer-atomic-term num-sig (ifze (su (su (ze))) (ze) (x) x))
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
