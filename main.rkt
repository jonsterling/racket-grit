#lang racket/base

;; This is based on David's ABT code, except that I have for now removed the 'sorts' stuff,
;; preferring only to work with numbers of bound variables. Separately, I will write a
;; typechecker once I have this working at an untyped level.

(require
 (for-syntax
  racket/base racket/list syntax/parse racket/syntax
  (for-syntax racket/base))
 racket/contract racket/fixnum racket/function racket/list racket/match racket/provide-syntax
 racket/set racket/string)

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


(struct scope (valence body)
  #:methods gen:custom-write
  [(define (write-proc sc port mode)
     (define temps (fresh-print-names (scope-valence sc)))
     (define binder
       (string-append
        "⟨"
        (string-join
         (for/list ([x temps])
           (format "~a" x))
         ", ")
        "⟩"))
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port "#<sc ~a.~a>" binder (scope-body sc))))]

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
     (scope valence (inst body (+ i valence)) new-exprs)))
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

(struct telescope (items)
  #:methods gen:custom-write
  [(define (write-proc tl port mode)
     (define items (telescope-items tl))
     (define num-items (length items))
     (define temps (fresh-print-names num-items))
     (for/list
         ([i (in-range 0 num-items)]
          [x temps]
          [item items])
       (define temps-slice (take temps i))
       (fprintf port "~a:" x)
       (parameterize ([used-names (append temps-slice (used-names))])
         (fprintf port "~a~a" (scope-body item) (if (< i (- num-items 1)) ", " "")))))]

  #:property prop:bindings
  (binder
   (lambda (tl frees i)
     (define (go item)
       (match-define (binder abs _) (bindings-accessor item))
       (abs item frees i))
     (telescope (map go (telescope-items tl))))
   (lambda (tl i new-exprs)
     (define (go item)
       (match-define (binder _ inst) (bindings-accessor item))
       (inst item i new-exprs))
     (map go (telescope-items tl))))

  #:methods gen:equal+hash
  ((define (equal-proc tl1 tl2 rec-equal?)
     (and (rec-equal? (telescope-items tl1) (telescope-items tl2))))
   (define (hash-proc tl rec-hash)
     (rec-hash (telescope-items tl)))
   (define (hash2-proc tl rec-hash2)
     (rec-hash2 (telescope-items tl)))))

(struct pi-type (domain codomain)
  #:methods gen:custom-write
  ((define (write-proc pi port mode)
     (match-define (pi-type tl sc) pi)
     (match-define (scope vl body) sc)
     (define temps (fresh-print-names vl))
     (fprintf port "{~a}" tl)
     (parameterize ([used-names (append temps (used-names))])
       (fprintf port " --> ~a" body))))

  #:property prop:bindings
  (binder
   (lambda (pi frees i)
     (match-define (pi-type tl sc) pi)
     (match-define (binder abs-tl _) (bindings-accessor tl))
     (match-define (binder abs-sc _) (bindings-accessor sc))
     (pi (abs-tl tl frees i) (abs-sc sc frees i)))
   (lambda (pi i new-exprs)
     (match-define (pi-type tl sc) pi)
     (match-define (binder _ inst-tl) (bindings-accessor tl))
     (match-define (binder _ inst-sc) (bindings-accessor sc))
     (pi (inst-tl tl i new-exprs) (inst-sc sc i new-exprs))))

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


(define/contract (inst sc vals)
  (->i ((sc scope?)
        (vals list?))
       #:pre (sc vals) (= (scope-valence sc) (length vals))
       (result any/c))
  (define open-expr (scope-body sc))
  (match-let ([(binder _ inst) (bindings-accessor open-expr)])
    (inst open-expr 0 vals)))

(define/contract (distinct? frees)
  (-> (listof free-name?) boolean?)
  (define seen (mutable-set))
  (for/and ([var frees])
    (begin0 (not (set-member? seen var))
      (set-add! seen var))))


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

(module+ test
  (pi-type
   (telescope (list (in-scope () (fresh)) (in-scope (a) a) (in-scope (a b) b)))
   (in-scope (a b c) a))

  (let ([x (fresh "hello")])
    (check-equal?
     (telescope (list (in-scope () x) (in-scope (a) a)))
     (telescope (list (in-scope () x) (in-scope (b) b)))))

  (check-equal?
   (in-scope (n m) n)
   (in-scope (a b) a)))
