#lang racket/base

(require racket/fixnum racket/match racket/contract racket/set)

(provide
 (contract-out
  [can-bind? (-> any/c boolean?)]
  [binder-arity (-> can-bind? exact-nonnegative-integer?)]

  [lf? (-> any/c boolean?)]

  [var? (-> any/c boolean?)]
  [var (->i ([binder can-bind?]
             [index (binder) (and/c exact-nonnegative-integer?
                                    (</c (binder-arity binder)))])
            [_ var?])]
  [var-binder (-> var? can-bind?)]
  [var-index (->i ([v var?])
                  [_ (v) (and/c exact-nonnegative-integer?
                                (</c (binder-arity (var-binder v))))])]
  [var-name (-> var? symbol?)]

  [SORT? (-> any/c boolean?)]
  [SORT (-> SORT?)]

  [arity? (-> any/c boolean?)]
  [arity (->i ([Ψ telescope?]
               [body (Ψ) (dynamic->*
                          #:mandatory-domain-contracts (build-list (length (telescope->list Ψ))
                                                                   (lambda (_) var?))
                          #:range-contracts (list (or/c plug? SORT?)))])
              [_ arity?])]
  [arity-domain (-> arity? telescope?)]
  [arity-codomain (-> arity? (or/c plug? SORT?))]

  [empty-tele (-> telescope?)]
  [empty-tele? (-> any/c boolean?)]

  [cons-tele (-> symbol? arity? (-> var? telescope?)
                 telescope?)]
  [cons-tele? (-> any/c boolean?)]
  [cons-tele-name (-> cons-tele? symbol?)]
  [cons-tele-type (-> cons-tele? arity?)]
  [cons-tele-telescope (-> cons-tele? telescope?)]

  [telescope? (-> any/c boolean?)]
  [telescope->list (-> telescope? (listof telescope?))]
  [telescope->alist (-> telescope? (listof (cons/c symbol? arity?)))]

  [bind? (-> any/c boolean?)]
  [bind (->i ([arg-names (listof symbol?)]
              [scope (arg-names) (dynamic->*
                                  #:mandatory-domain-contracts (build-list (length arg-names) (lambda (_) var?))
                                  #:range-contracts (list plug?))])
             [_ bind?])]
  [bind-vars (-> bind? (listof symbol?))]
  [bind-scope (-> bind? plug?)]

  [plug? (-> any/c boolean?)]
  [plug-var (-> plug? var?)]
  [plug-spine (-> plug? (listof bind?))]
  [plug (->* (var?) ()
             #:rest (listof bind?)
             plug?)]

  [unwrap-nullary (-> lf? lf?)]

  [as-arity (-> (or/c var? SORT? plug? arity?)
                arity?)]
  [as-plug (-> (or/c var? plug?)
               plug?)]
  [as-base-classifier (-> (or/c SORT? var? plug?)
                          (or/c SORT? plug?))]
  [as-bind (-> (or/c var? plug? bind?) bind?)]

  [subst (-> lf? (listof lf?) telescope?
               lf?)]
  [rename-to-telescope (-> lf? (listof var?) telescope?
                           lf?)]))

(define (can-bind? b)
  (or (bind? b) (cons-tele? b)))

(define (binder-arity b)
  (cond [(cons-tele? b) 1]
        [(bind? b) (length (bind-vars b))]))


(define (var-name v)
  (let ((binder (var-binder v))
        (index (var-index v)))
   (cond [(cons-tele? binder)
          (cons-tele-name binder)]
         [(bind? binder)
          (list-ref (bind-vars binder) index)]
         [else (error 'bad-binder)])))

(define used-names (make-parameter (set)))
(define name-displays (make-parameter (hash)))

(define (get-name x)
  (define (step y)
    (string->symbol (string-append (symbol->string y) "*")))
  (if (set-member? (used-names) x)
      (get-name (step x))
      x))

;; Variables are a pair of a pointer to their binding site and a
;; natural number stating which bound variable they are
(struct var (binder index)
  #:extra-constructor-name make-var
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc v port mode)
     (define to-show (hash-ref (name-displays) v #f))
     (if to-show
         (fprintf port "~a" to-show)
         (fprintf port "#<var:~s>"
                  (var-name v))))])

(struct SORT ()
  #:transparent
  #:methods gen:custom-write
  [(define (write-proc s port mode)
     (fprintf port "SORT"))])

(define (telescope->alist tele)
  (cond [(empty-tele? tele) '()]
        [(cons-tele? tele)
         (cons (cons (cons-tele-name tele) (cons-tele-type tele))
               (telescope->alist (cons-tele-telescope tele)))]))

(define (telescope->list x)
  (if (empty-tele? x)
      '()
      (cons x (telescope->list (cons-tele-telescope x)))))

(define (telescope? x)
  (or (empty-tele? x) (cons-tele? x)))


(define (print-telescope tele port)
  (fprintf port "(")
  (let loop ([Ψ tele])
   (if (cons-tele? Ψ)
       (let ([x (get-name (cons-tele-name Ψ))])
         (fprintf port "[~a ~a]" x (cons-tele-type Ψ))
         (parameterize ([used-names (set-add (used-names) x)]
                        [name-displays (hash-set (name-displays) (var Ψ 0) x)])
           (loop (cons-tele-telescope Ψ))))
       (begin (fprintf port ")")
              (values (used-names) (name-displays))))))

(struct empty-tele () #:transparent
  #:methods gen:custom-write
  [(define (write-proc s port mode)
     (print-telescope s port)
     (void))])

(struct cons-tele (name type [telescope-internal #:mutable])
  #:constructor-name make-cons-tele
  #:omit-define-syntaxes
  #:methods gen:custom-write
  [(define (write-proc s port mode)
     (print-telescope s port)
     (void))]
  #:methods gen:equal+hash
  [(define (equal-proc cons-tele-1 cons-tele-2 rec-equal?)
     ;; Ignore the name hint
     (and (rec-equal? (cons-tele-type cons-tele-1)
                      (cons-tele-type cons-tele-2))
          (rec-equal? (cons-tele-telescope cons-tele-1)
                      (cons-tele-telescope cons-tele-2))))
   (define (hash-proc tele rec-hash)
     (fxxor (rec-hash (cons-tele-type tele))
            (rec-hash (cons-tele-telescope tele))))
   (define (hash2-proc tele rec-hash)
     (fxxor (rec-hash (cons-tele-type tele))
            (rec-hash (cons-tele-telescope tele))))])

(define (cons-tele name type sc)
  (define Ψ (make-cons-tele name type #f))
  (define sc-val (sc (var Ψ 0)))
  (set-cons-tele-telescope-internal! Ψ sc-val)
  Ψ)

(define (cons-tele-telescope tele)
  (cons-tele-telescope-internal tele))

;; domain is a telescope that binds variables also visible in the codomain
(struct arity (domain [codomain-internal #:mutable])
  #:omit-define-syntaxes
  #:constructor-name make-arity
  #:methods gen:custom-write
  [(define (write-proc a port mode)
     (fprintf port "(arity ")
     (define-values (used displayed)
       (print-telescope (arity-domain a) port))
     (parameterize ([used-names used]
                    [name-displays displayed])
       (fprintf port " ~s)" (arity-codomain a))))]
  #:methods gen:equal+hash
  [(define (equal-proc arity1 arity2 rec-equal?)
     ;; Ignore the bound names
     (and (rec-equal? (arity-domain arity1)
                      (arity-domain arity2))
          (rec-equal? (arity-codomain arity1)
                      (arity-codomain arity2))))
   (define (hash-proc ar rec-hash)
     (fxxor (rec-hash (map cdr (telescope->alist (arity-domain ar))))
            (rec-hash (arity-codomain ar))))
   (define (hash2-proc ar rec-hash)
     (fxxor (rec-hash (map cdr (telescope->alist (arity-domain ar))))
            (rec-hash (arity-codomain ar))))])

(define (arity dom cod)
  (define ar (make-arity dom #f))
  (set-arity-codomain-internal! ar (apply cod
                                          (for/list ([b (telescope->list dom)])
                                            (var b 0))))
  ar)

(define (arity-codomain ar)
  (arity-codomain-internal ar))

;; vars is a list of variable names, scope is an LF term or a
;; function from the binder to an LF term. The first time the
;; function is called, the result is memoized.
(struct bind (vars [scope-internal #:mutable])
  #:omit-define-syntaxes
  #:constructor-name make-bind
  #:methods gen:custom-write
  [(define (write-proc b port mode)
     (fprintf port "(bind (")
     (let loop ([vars (bind-vars b)]
                [i 0])
       (if (pair? vars)
           (let ([x (get-name (car vars))])
             (fprintf port "~a" x)
             (unless (null? (cdr vars)) (fprintf port " "))
             (parameterize ([used-names (set-add (used-names) x)]
                            [name-displays (hash-set (name-displays) (var b i) x)])
               (loop (cdr vars) (add1 i))))
           (begin (fprintf port ") ~a)" (bind-scope b))))))]
  #:methods gen:equal+hash
  [(define (equal-proc b1 b2 rec-equal?)
     (rec-equal? (bind-scope b1) (bind-scope b2)))
   (define (hash-proc b rec-hash)
     (rec-hash b))
   (define (hash2-proc b rec-hash)
     (rec-hash b))])

(define (bind vars sc)
  (define b (make-bind vars #f))
  (define sc-val
    (apply sc (for/list ([i (in-range (length vars))])
                (var b i))))
  (set-bind-scope-internal! b sc-val)
  b)

(define (bind-scope b)
  (bind-scope-internal b))

;; var must be a ref, spine a list of expressions
(struct plug (var spine)
  #:transparent
  #:omit-define-syntaxes
  #:constructor-name make-plug
  #:methods gen:custom-write
  [(define (write-proc p port mode)
     (if (pair? (plug-spine p))
         (begin (fprintf port "(plug ~s" (plug-var p))
                (for ([arg (plug-spine p)])
                  (display " " port)
                  (display arg port))
                (display ")" port))
         (begin (display "(" port)
                (write (plug-var p) port)
                (display ")" port))))])

(define (plug x . σ)
  (make-plug x σ))

(define (intersperse l1 l2)
  (match* (l1 l2)
    [('() '()) '()]
    [((cons x xs) (cons y ys))
     (cons x (cons y (intersperse xs ys)))]
    [(_ _)
     (raise-arguments-error 'intersperse
                            "Lengths of lists are not the same"
                            "first list" l1
                            "second list" l2)]))

  (struct exn:fail:lf-syntax exn:fail (val)
    #:extra-constructor-name make-exn:fail:lf-syntax)

  (define (raise-bad-lf-syntax v)
    (raise (make-exn:fail:lf-syntax (format "Bad LF syntax: ~a" v)
                                    (current-continuation-marks)
                                    v)))

(define (unwrap-nullary e)
  (cond
    [(and (arity? e) (empty-tele? (arity-domain e)))
     (unwrap-nullary (arity-codomain e))]
    [(and (bind? e) (null? (bind-vars e)))
     (unwrap-nullary (bind-scope e))]
    [else e]))

(define (as-plug e)
  (cond
    [(var? e)
     (as-plug (plug e))]
    [(plug? e)
     e]
    [else (raise-bad-lf-syntax e)]))

(define (as-base-classifier e)
  (cond
    [(SORT? e) e]
    [else (as-plug e)]))

(define (as-arity e)
  (if (arity? e)
      e
      (arity (empty-tele)
             (lambda () (as-base-classifier e)))))

(define (as-bind e)
  (cond [(bind? e) e]
        [(or (plug? e) (var? e))
         (bind '() (lambda () (as-plug e)))]
        [else (raise-bad-lf-syntax e)]))

(define (lf? e)
  (or (SORT? e) (arity? e) (plug? e) (var? e) (bind? e)))


(define (rename-to-telescope expr xs Ψ)
  (define ρ
    (for/hash ([x xs]
               [b (telescope->list Ψ)])
      (values x (var b 0))))
  (do-subst ρ expr))

(define (subst expr σ Ψ)
  (define ρ
    (for/hash ([b (telescope->list Ψ)]
               [val σ])
      (values (var b 0) val)))

  (do-subst ρ expr))

(define (do-subst ρ e)
  (match e
    [(? var? x)
     (define val (hash-ref ρ x #f))
     (if val val x)]
    [(? arity?
        (app arity-domain dom)
        (app arity-codomain cod))
     (define Ψ (do-subst ρ dom))
     (arity Ψ
            (lambda vs
              (do-subst (let loop ([old-ρ ρ]
                                   [vars vs]
                                   [old-dom dom])
                          (if (pair? old-dom)
                              (loop (hash-set old-ρ (var old-dom 0) (car vars))
                                    (cdr vars)
                                    (cons-tele-telescope old-dom))
                              old-ρ))
                        cod)))]
    [(? bind?
        b
        (app bind-vars vars)
        (app bind-scope sc))
     (bind vars
           (lambda xs
             ;; Extend the environment with a renaming from the
             ;; old bound vars to the new
             (define ρ*
               (let loop ([old-ρ ρ]
                          [new-vars xs]
                          [i 0])
                 (if (pair? new-vars)
                     (loop (hash-set old-ρ (var b i) (car new-vars))
                           (cdr new-vars)
                           (add1 i))
                     old-ρ)))
             (do-subst ρ* sc)))]
    [(? plug?
        (app plug-var var)
        (app plug-spine spine))
     (define new-spine
       (for/list ([arg spine])
         (do-subst ρ arg)))
     (define var-val
       (hash-ref ρ var #f))
     (match var-val
       [(? bind? b)
        (define var-count (length (bind-vars b)))
        (do-subst
         (let loop ([old-ρ ρ]
                    [i 0]
                    [sp new-spine])
           (if (pair? sp)
               (loop (hash-set old-ρ (var b i) (car sp))
                     (add1 i)
                     (cdr sp))
               old-ρ))
         (bind-scope b))]
       [_ (apply plug var new-spine)])]
    [(? SORT?) e]
    [(? empty-tele?) e]
    [(? cons-tele?
        (app cons-tele-name x)
        (app cons-tele-type t)
        (app cons-tele-telescope more))
     (cons-tele x (do-subst ρ t) (lambda (y) (do-subst (hash-set ρ (var e 0) y) more)))]))
