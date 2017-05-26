#lang racket/base

;; This is based on David's ABT code, except that I hav for now removed the 'sorts' stuff,
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

; TODO: define equal+hash
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

(define-match-expander in-scope
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (with-syntax ([var-count (length (syntax->list #'(x ...)))])
         #'(? (lambda (sc) (and (scope? sc) (= (scope-valence sc) var-count)))
              (app auto-inst
                   (cons (list x ...) body))))]))
  (lambda (stx)
    (syntax-parse stx
      [(_ (x:id ...)
          body:expr)
       (with-syntax ([(x-str ...) (map symbol->string (syntax->datum #'(x ...)))])
         (syntax/loc stx
           (let ([x (fresh x-str)] ...)
             (abs (list x ...) body))))])))


(module+ test
  (in-scope (n) n))
