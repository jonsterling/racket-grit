#lang racket/base

(require racket/contract racket/match)
(require (prefix-in ast: "ast.rkt") "typecheck.rkt")
(provide (contract-out
          [spec? (-> any/c boolean?)]
          [spec (-> symbol?
                    (or/c ast:arity? ast:SORT?)
                    spec?)]
          [spec-arity (-> spec? ast:arity?)]
          [judgment? (-> any/c boolean?)]
          [judgment (-> spec? (listof ast:bind?) judgment?)]
          [sequent? (-> any/c boolean?)]
          [sequent-telescope? (-> any/c boolean?)]
          [sequent-tele-nil (-> sequent-telescope?)]
          [≫ (-> sequent-telescope? judgment? sequent?)]
          [check-sequent (-> typing-context? sequent? ast:arity?)]))

(module+ test (require rackunit))

;; 𝔰 ::= Ψ ▷ τ (we re-use the Racket context, so there's no explicit
;; Σ, but each of these is a ϑ). The name is just a hint for display.
(struct spec (name arity)
  #:methods gen:custom-write
  [(define (write-proc 𝔰 port mod)
     (fprintf port "#<spec:~a>" (spec-name 𝔰)))])

;; Check the judgment Ψ ⊢ 𝔰 spec, throwing an exception if it does
;; not hold.
(define (check-spec Ψ 𝔰)
  (define α (spec-arity 𝔰))
  (well-formed-classifier Ψ α))

(module+ test
  (require "signature-syntax.rkt")
  (define-sig L
    ;; Propositions τ
    [τ () SORT]
    [⊤ () (τ)]
    [⊥ () (τ)]
    [∧ ([A (τ)] [B (τ)])
       (τ)]
    ;; Proofs P
    [P () SORT]
    [yep () (P)]
    [both ([p1 (P)] [p2 (P)])
          (P)])
  (define is-true (spec 'is-true (term L (arity ([what (τ)]) (P)))))
  (check-spec L is-true))

;; Judgments are the application of a named specification to a
;; suitable spine of arguments.
;; 𝒥 ::= ϑ[ψ]
(struct judgment (spec args)
  #:methods gen:custom-write
  [(define (write-proc 𝒥 port mod)
     (define ϑ (spec-name (judgment-spec 𝒥)))
     (define ψ (judgment-args 𝒥))
     (fprintf port "(~a" ϑ)
     (for ([arg ψ])
       (display " " port)
       (display arg port))
     (display ")" port))])



;; Return the erasure sort of a well-formed judgment
(define (check-judgment Ψ 𝒥)
  (match-define (judgment (and 𝔰 (spec ϑ α)) φ) 𝒥)
  (define Φ (ast:arity-domain α))
  (define τ (ast:arity-codomain α))
  (check-spec Ψ 𝔰)
  (check-spine Ψ φ Φ)
  (ast:subst τ φ Φ))

(module+ test
  (define and-true
    (judgment is-true (list (ast:as-bind (term L (∧ (⊤) (⊤)))))))
  (define false-true
    (judgment is-true (list (ast:as-bind (term L (⊥))))))
  ;; Both judgments are well-formed
  (check-true (ast:plug? (check-judgment L and-true)))
  (check-true (ast:plug? (check-judgment L false-true))))

;; 𝒮 ::= ℋ ≫ 𝒥
(struct ≫ (hypotheses conclusion))

(define (sequent? x)
  (≫? x))

;; ℋ ::= · | ℋ, x : 𝒮

;; Telescopes for sequents are stored as a structure that parallels LF
;; telescopes.  Each sequent telescope has a pointer to its LF
;; realization, which is maintained separately. The snoc operator for
;; sequent telescopes constructs the underlying LF telescope by
;; performing extraction on the provided sequent.
(struct sequent-tele-nil ())
(struct sequent-tele-snoc (prev refines sequent))

(define (make-sequent-tele-snoc Ψ prev x 𝒮)
  (define prev′ (erase-sequent-tele prev))
  (define Φ (ast:snoc-tele prev′ x (check-sequent Ψ 𝒮)))
  (sequent-tele-snoc prev Φ 𝒮))

(define (erase-sequent-tele ℋ)
  (match ℋ
    [(sequent-tele-nil) (ast:empty-tele)]
    [(sequent-tele-snoc _ Φ _) Φ]))

(define (sequent-telescope? x)
  (or (sequent-tele-snoc? x)
      (sequent-tele-nil? x)))


(define (check-sequent Ψ 𝒮)
  (match-define (≫ ℋ 𝒥) 𝒮)
  (define Φ (erase-sequent-tele ℋ))
  (define τ (check-judgment (extend-context Ψ Φ) 𝒥))
  (ast:arity Φ (lambda _ τ)))

(module+ test
  (define indeed (≫ (sequent-tele-nil) and-true))
  (check-equal? (check-sequent L indeed) (term L (arity () (P))))
  (define perhaps
    (≫ (make-sequent-tele-snoc L
                               (sequent-tele-nil)
                               'nope
                               (≫ (sequent-tele-nil) false-true))
       false-true))
  (check-equal? (check-sequent L perhaps)
                (term L (arity ([nuh-uh (P)])
                               (P))))
)
