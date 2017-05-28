#lang racket/base

;; This is based on David's ABT code, except that I have for now removed the 'sorts' stuff,
;; preferring only to work with numbers of bound variables. Separately, I will write a
;; typechecker once I have this working at an untyped level.

(require
 (for-syntax
  racket/base racket/list syntax/parse racket/syntax
  (for-syntax racket/base))
 racket/contract racket/fixnum racket/function racket/list racket/match racket/provide-syntax
 racket/set racket/string racket/dict)

(module+ test
  (require rackunit))

(define used-names (make-parameter '()))

(define/contract (string-incr hint)
  (-> string? string?)
  (define last-char (string-ref hint (sub1 (string-length hint))))
  (if (char=? last-char #\z)
      (string-append hint "a")
      (string-append
       (substring hint 0 (sub1 (string-length hint)))
       (string (integer->char (add1 (char->integer last-char)))))))

(module+ test
  (check-equal? (string-incr "a") "b")
  (check-equal? (string-incr "z") "za"))

(define/contract (next-name hint used)
  (-> string? (listof string?) string?)
  (if (member hint used)
      (next-name (string-incr hint) used)
      hint))

(module+ test
  (check-equal? (next-name "aa" '("aa")) "ab")
  (check-equal? (next-name "az" '("az")) "aza"))

(define/contract (fresh-print-names n)
  (->i ((n exact-nonnegative-integer?))
       (result (n) (and/c (listof string?)
                          (lambda (r) (= (length r) n)))))
  (if (zero? n)
      '()
      (let ((x (next-name "a" (used-names))))
        (parameterize ([used-names (cons x (used-names))])
          (cons x (fresh-print-names (sub1 n)))))))


(struct binder (abs inst) #:transparent)

(define-values (prop:bindings has-prop:bindings? bindings-accessor)
  (make-struct-type-property
   'bindings
   (lambda (v _)
     (and (binder? v) v))))

(define (bindings? v)
  (has-prop:bindings? v))


(struct bound-name (index)
  #:transparent
  #:property prop:bindings
  (binder
   (lambda (expr frees i) expr)
   (lambda (expr i new-exprs)
     (define j (- (bound-name-index expr) i))
     (if (<= 0 j (add1 (length new-exprs)))
         (list-ref new-exprs j)
         expr)))

  #:methods gen:custom-write
  ((define (write-proc x port mode)
     (define print-x
       (let loop ((i (bound-name-index x))
                  (used (used-names)))
         (if (zero? i)
             (if (pair? used)
                 (car used)
                 (format "#<~a>" (bound-name-index x)))
             (if (pair? used)
                 (loop (sub1 i) (cdr used))
                 (format "#<~a>" (bound-name-index x))))))
     (write-string print-x port))))

(struct free-name (sym hint)
  #:property prop:bindings
  (binder
   (lambda (expr frees i)
     (let ((j (index-of frees expr (lambda (x y) (eqv? (free-name-sym x) (free-name-sym y))))))
       (if j (bound-name (+ i j)) expr)))
   (lambda (expr i new-exprs)
     expr))
  #:methods gen:custom-write
  ((define (write-proc x port mode)
     (fprintf port "#<free:~a>" (free-name-sym x))))
  #:methods gen:equal+hash
  ((define (equal-proc fn1 fn2 rec-equal?)
     (eqv? (free-name-sym fn1) (free-name-sym fn2)))
   (define (hash-proc fn rec-hash)
     (rec-hash (free-name-sym fn)))
   (define (hash2-proc fn rec-hash2)
     (rec-hash2 (free-name-sym fn)))))

(define (fresh (str "x"))
  (free-name (gensym str) str))


(define/contract (distinct? frees)
  (-> (listof free-name?) boolean?)
  (define seen (mutable-set))
  (for/and ([var frees])
    (begin0 (not (set-member? seen var))
      (set-add! seen var))))


(struct scope (valence body)
  #:methods gen:custom-write
  [(define (write-proc sc port mode)
     (define temps (fresh-print-names (scope-valence sc)))
     (define binder (string-join (for/list ([x temps]) (format "~a" x)) ", "))
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port "#<sc ⟨~a⟩.~a>" binder (scope-body sc))))]

  #:property prop:bindings
  (binder
   (lambda (sc frees i)
     (define valence (scope-valence sc))
     (define body (scope-body sc))
     (match-define (binder abs _) (bindings-accessor body))
     (scope valence (abs body frees (+ i valence))))
   (lambda (sc i new-exprs)
     (define valence (scope-valence sc))
     (define body (scope-body sc))
     (match-define (binder _ inst) (bindings-accessor body))
     (scope valence (inst body (+ i valence) new-exprs))))
  #:methods gen:equal+hash
  ((define (equal-proc sc1 sc2 rec-equal?)
     (and (rec-equal? (scope-valence sc1) (scope-valence sc2))
          (rec-equal? (scope-body sc1) (scope-body sc2))))
   (define (hash-proc sc rec-hash)
     (fxxor (rec-hash (scope-valence sc))
            (rec-hash (scope-body sc))))
   (define (hash2-proc sc rec-hash2)
     (fxxor (rec-hash2 (scope-valence sc))
            (rec-hash2 (scope-body sc))))))

(define (write-proc/telescope cells port mode)
  (define len (length cells))
  (define temps (fresh-print-names len))
  (for/list ([i (in-range 0 len)]
             [x temps]
             [cell cells])
    (define slice (take temps i))
    (fprintf port "~a:" x)
    (parameterize ([used-names (append slice (used-names))])
      (fprintf port "~a~a" (scope-body cell) (if (< i (- len 1)) ", " "")))))

(define bindings/telescope
  (binder
   (lambda (cells frees i)
     (define (go cell)
       (match-define (binder abs _) (bindings-accessor cells))
       (abs cell frees i))
     (map go cells))
   (lambda (cells i new-exprs)
     (define (go cell)
       (match-define (binder _ inst) (bindings-accessor cell))
       (inst cell i new-exprs))
     (map go cells))))



(define/contract (inst sc vals)
  (->i ((sc scope?)
        (vals list?))
       #:pre (sc vals) (= (scope-valence sc) (length vals))
       (result any/c))
  (define open-expr (scope-body sc))
  (match-let ([(binder _ inst) (bindings-accessor open-expr)])
    (inst open-expr 0 vals)))


(define/contract (abs frees closed-expr)
  (->i ((frees (and/c (listof free-name?) distinct?))
        (closed-expr bindings?))
       (result
        (frees)
        (and/c scope? (lambda (r) (= (scope-valence r) (length frees))))))
  (define open-expr
    (match-let ([(binder abs _) (bindings-accessor closed-expr)])
      (abs closed-expr frees 0)))
  (scope (length frees) open-expr))

(define (auto-inst sc)
  (define frees (build-list (scope-valence sc) (lambda (i) (fresh))))
  (cons frees (inst sc frees)))



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
     (match (dict-ref ctx x)
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

  (define my-tm
    (Π (x (Π (TYPE))) ($ x)))

  my-tm
  (chk-type '() my-tm)


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
