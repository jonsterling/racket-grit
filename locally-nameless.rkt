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
 racket/list
 racket/match
 racket/provide-syntax
 racket/set
 racket/string)

(provide
 prop:bindings
 bindings-accessor
 fresh-print-names

 (contract-out
  (struct binder
    ((abs (-> any/c (listof free-name?) integer? any/c))
     (inst (-> any/c integer? (listof bindings?) any/c))))

  (struct scope
    ((valence integer?)
     (body bindings?)))

  (struct bound-name
    ((index integer?)))

  (struct free-name
    ((sym symbol?)
     (hint string?))))

 bindings/telescope
 write-proc/telescope
 used-names
 fresh
 instantiate abstract auto-instantiate
 in-scope)

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
                          (λ (r) (= (length r) n)))))
  (if (zero? n)
      '()
      (let ((x (next-name "a" (used-names))))
        (parameterize ([used-names (cons x (used-names))])
          (cons x (fresh-print-names (sub1 n)))))))


(struct binder (abs inst) #:transparent)

(define-values (prop:bindings has-prop:bindings? bindings-accessor)
  (make-struct-type-property
   'bindings
   (λ (v _)
     (and (binder? v) v))))

(define (bindings? v)
  (has-prop:bindings? v))


(struct bound-name (index)
  #:transparent
  #:property prop:bindings
  (binder
   (λ (expr frees i) expr)
   (λ (expr i new-exprs)
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
   (λ (expr frees i)
     (let ((j (index-of frees expr (lambda (x y) (eqv? (free-name-sym x) (free-name-sym y))))))
       (if j (bound-name (+ i j)) expr)))
   (λ (expr i new-exprs)
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

(define (op-name sym)
  (free-name sym (symbol->string sym)))

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
   (λ (sc frees i)
     (define valence (scope-valence sc))
     (define body (scope-body sc))
     (match-define (binder abs _) (bindings-accessor body))
     (scope valence (abs body frees (+ i valence))))
   (λ (sc i new-exprs)
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
   (λ (cells frees i)
     (define (go cell)
       (match-define (binder abs _) (bindings-accessor cell))
       (abs cell frees i))
     (map go cells))
   (λ (cells i new-exprs)
     (define (go cell)
       (match-define (binder _ inst) (bindings-accessor cell))
       (inst cell i new-exprs))
     (map go cells))))



(define/contract (instantiate sc vals)
  (->i ((sc scope?)
        (vals list?))
       #:pre (sc vals) (= (scope-valence sc) (length vals))
       (result any/c))
  (define open-expr (scope-body sc))
  (match-let ([(binder _ inst) (bindings-accessor open-expr)])
    (inst open-expr 0 vals)))


(define/contract (abstract frees closed-expr)
  (->i ((frees (and/c (listof free-name?) distinct?))
        (closed-expr bindings?))
       (result
        (frees)
        (and/c scope? (λ (r) (= (scope-valence r) (length frees))))))
  (define open-expr
    (match-let ([(binder abs _) (bindings-accessor closed-expr)])
      (abs closed-expr frees 0)))
  (scope (length frees) open-expr))

(define (auto-instantiate sc)
  (define frees (build-list (scope-valence sc) (λ (i) (fresh))))
  (cons frees (instantiate sc frees)))


(define-match-expander in-scope
  ; destructor
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (with-syntax ([var-count (length (syntax->list #'(x ...)))])
         #'(? (λ (sc) (and (scope? sc) (= (scope-valence sc) var-count)))
              (app auto-instantiate (cons (list x ...) body))))]))

  ; constructor
  (λ (stx)
    (syntax-parse stx
      [(_ (x:id ...) body:expr)
       (with-syntax ([(x-str ...) (map symbol->string (syntax->datum #'(x ...)))])
         (syntax/loc stx
           (let ([x (fresh x-str)] ...)
             (abstract (list x ...) body))))])))