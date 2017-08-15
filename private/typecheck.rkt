#lang racket/base

(require racket/match racket/contract "ast.rkt")

(provide
 (contract-out
  [typing-context? (-> any/c boolean?)]
  [empty-ctx typing-context?]
  [extend-context (-> typing-context? telescope? typing-context?)]
  [context->list (-> typing-context? (listof telescope?))]

  [well-formed-classifier (-> typing-context? arity? void?)]
  [well-formed-context (-> typing-context? void?)]
  [check-type (-> typing-context? bind? arity? void?)]
  [synth (-> typing-context? plug? (or/c SORT? plug?))]))


(struct typing-context (telescopes)
  #:methods gen:custom-write
  [(define (write-proc Γ port mode)
     (fprintf port "~a" (apply append
                               (map telescope->alist
                                    (typing-context-telescopes Γ)))))])

(define empty-ctx (typing-context '()))

(define (extend-context Γ Ψ)
  (typing-context (cons Ψ (typing-context-telescopes Γ))))

(define (context->list Γ)
  (apply append (map telescope->list (typing-context-telescopes Γ))))

(define (lookup x Γ)
  (let outer ([teles (typing-context-telescopes Γ)])
    (if (pair? teles)
        (let inner ([Ψ (car teles)])
          (if (cons-tele? Ψ)
              (if (eq? (var-binder x) Ψ)
                  (cons-tele-type Ψ)
                  (inner (cons-tele-telescope Ψ)))
              (outer (cdr teles))))
        (raise-bad-var x))))

(define (raise-type-mismatch expected found)
  (error (format "Expected: ~a but found ~a" expected found)))

(define (raise-bad-var x)
  (error (format "Unknown variable: ~a" x)))

(define (raise-not-arity t)
  (error (format "Not an arity: ~a" t)))


(define (raise-not-arity-or-sort t)
  (error (format "Not an arity or SORT: ~a" t)))

(define (raise-not-bind N)
  (error (format "Not a binder: ~a" N)))

(define (raise-spine-underflow Ψ)
  (error (format "Not enough variables in substitution. Leftovers: ~a" Ψ)))

(define (raise-spine-overflow σ)
  (error (format "Too many variables in substitution. Leftovers: ~a" σ)))

(define (is-arity t)
  (if (arity? t)
      (values (arity-domain t) (arity-codomain t))
      (raise-not-arity t)))

;; Check the judgment Γ ⊢ Ψ ctx. Returns (void) on success, throws an
;; exception on failure.
(define (telescope-ok Γ Ψ)
  (cond
    [(empty-tele? Ψ) (void)]
    [(cons-tele? Ψ)
     (begin (telescope-ok Γ (cons-tele-telescope Ψ))
            (well-formed-classifier (extend-context Γ Ψ) (cons-tele-type Ψ)))]))

(define (well-formed-context Γ)
  (let loop ([Ψs (typing-context-telescopes Γ)])
    (if (pair? Ψs)
        (begin (loop (cdr Ψs))
               (telescope-ok (typing-context (cdr Ψs)) (car Ψs)))
        (void))))

;; Check the judgment Γ ⊢ V ⇐ ok, (void) on success or exception on failure
(define (well-formed-classifier Γ V)
  (define Ψ (arity-domain V))
  (define cod (arity-codomain V))
  (begin (telescope-ok Γ Ψ)
         (if (or (SORT? cod)
                 (SORT? (synth (extend-context Γ Ψ) cod)))
             (void)
             (raise-not-arity-or-sort V))))

;; The judgment Γ ⊢ σ ⇐ Ψ. (void) on success, exn on failure.
(define (check-spine Γ σ Ψ)
  (match σ
    ['()
     (if (empty-tele? Ψ)
         (void)
         (raise-spine-underflow Ψ))]
    [(cons M σ-rest)
     (if (cons-tele? Ψ)
         (let ([x (var Ψ 0)]
               [V (cons-tele-type Ψ)])
           (check-type Γ M (subst V σ-rest Ψ)))
         (raise-spine-overflow σ))]))

;; The judgment Γ ⊢ N ⇐ V
(define (check-type Γ N V)
  (if (bind? N)
      (if (arity? V)
          (let* ([Ψ (arity-domain V)]
                 [ty (synth (extend-context Γ Ψ)
                            (rename-to-telescope (bind-scope N)
                                                 (for/list ([i (in-range (length (bind-vars N)))])
                                                   (var N i))
                                                 Ψ))])
            (if (equal? (arity-codomain V) ty)
                (void)
                (raise-type-mismatch (arity-codomain V) ty)))
          (raise-not-arity V))
      (raise-not-bind N)))

;; The judgment Γ ⊢ R ⇒ v (where v is output-moded).
(define (synth Γ R)
  (define-values (Ψ v) (is-arity (lookup (plug-var R) Γ)))
  (check-spine Γ (plug-spine R) Ψ)
  (define out (subst v (plug-spine R) Ψ))
  (if (SORT? out) out (as-plug out)))
