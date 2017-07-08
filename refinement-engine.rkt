#lang racket/base

(require
  (for-syntax
   racket/base
   syntax/parse
   syntax/srcloc)
  racket/contract
  racket/match
  racket/dict
  syntax/srcloc
  "locally-nameless.rkt"
  "logical-framework.rkt")


(module+ test (require rackunit))
(provide
 unapply
 with-hyp
 splice-context
 define-rule
 probe
 multicut
 orelse
 id-tac
 >> plug* bind*
 raise-refinement-error)



(define refinement-ctx?
  (listof
   (cons/c
    free-name?
    arity?)))

(define/contract (check-sort-refinement ctx rctx refn)
  (-> ctx? refinement-ctx? plug? sort?)
  (define args (plug-spine refn))
  (define arity (dict-ref rctx (plug-var refn)))
  (check-spine ctx (arity-domain arity) args)
  (instantiate (arity-codomain arity) args))

; TODO: check this code and make sure it is correct
(define/contract (check-telescope-refinement ctx rctx tele)
  (-> ctx? refinement-ctx? tele? ctx?)
  (define (aux ctx env input output)
    (match input
      ['() output]
      [(cons sc tele)
       (define arity (check-arity-refinement ctx rctx (instantiate sc env)))
       (define x (fresh))
       (aux
        (ctx-set ctx x arity)
        (append env (list x))
        (append output (list (cons x arity))))]))
  (aux ctx '()  tele '()))

(define/contract (check-arity-refinement ctx rctx refn)
  (-> ctx? refinement-ctx? arity? arity?)
  (define dom (arity-domain refn))
  (define cod (arity-codomain refn))
  (define dom-ctx (check-telescope-refinement ctx rctx dom))
  (check-sort-refinement
   (append ctx dom-ctx)
   rctx
   (instantiate cod (map car dom-ctx))))



(module hyp-pattern racket/base
  (require
    (for-syntax racket/base syntax/parse)
    racket/list
    racket/match
    racket/contract
    "logical-framework.rkt"
    "locally-nameless.rkt")
  (provide with-hyp unapply)

  (define/contract (ctx-split Γ x)
    (-> ctx? free-name? (values ctx? arity? (-> any/c ctx?)))
    (define (pred cell)
      (not (equal? x (car cell))))

    (define Γ0 (takef Γ pred))
    (define Γ1 (cdr (dropf Γ pred)))

    (values
     Γ0
     (ctx-ref Γ x)
     (λ (e)
       ctx-map
       (λ (a) (instantiate (abstract (list x) a) (list (as-term e))))
       Γ1)))

  (define-for-syntax ctx-split-expander
    (λ (stx)
      (syntax-parse stx
        [(_ Γ0:expr x:expr ((y:id B:expr) ...) A:expr Γ1:expr)
         (syntax/loc stx
           (app (λ (Γ) (ctx-split Γ x)) Γ0 (arity ((y B) ...) A) Γ1))])))

  (define-for-syntax unapply-hyp-expander
    (λ (stx)
      (syntax-parse stx
        [(_ f:expr x:expr ...)
         (syntax/loc stx
           (app
            (λ (e)
              (λ (ex . exs)
                (instantiate
                    (abstract (list x ...) e)
                  (cons (as-term ex) (map as-term exs)))))
            f))])))

  (define-match-expander with-hyp
    ctx-split-expander)

  (define-match-expander unapply
    unapply-hyp-expander))

(require 'hyp-pattern)

(define-syntax (splice-context stx)
  (syntax-parse stx
    [(_ Γ0:expr ((x:expr ty:expr) ...) Γ1:expr)
     (syntax/loc stx
       (append Γ0
               (list (cons x (as-arity ty)) ...)
               Γ1))]))

(module sequent racket/base
  (require
    (for-syntax racket/base syntax/parse)
    "locally-nameless.rkt"
    "logical-framework.rkt"
    racket/match
    racket/contract)
  (provide >> subgoals >>? >>-ty
           proof-state proof-state? >: complete-proof? proof-extract)

  ;; This is a wrapper around a goal which keeps a cache of names for assumptions,
  ;; which can then be used when unpacking. The result of this is that we can have user-supplied
  ;; names in tactic scripts, even though naively that doesn't make scope-sense when thinking
  ;; of goals as arities.
  (struct >> (names ty)
    #:omit-define-syntaxes
    #:extra-constructor-name make->>
    #:transparent
    #:property prop:bindings
    (bindings-support
     (λ (goal frees i)
       (define names (>>-names goal))
       (define ty (>>-ty goal))
       (match-define(bindings-support abs-ty _) (bindings-accessor ty))
       (make->> names (abs-ty ty frees i)))
     (λ (goal i new-exprs)
       (define names (>>-names goal))
       (define ty (>>-ty goal))
       (match-define(bindings-support _ inst-ty) (bindings-accessor ty))
       (make->> names (inst-ty ty i new-exprs)))))

  ;; a telescope of goals, together with an extract (scope) binding the goals' plugvariables
  (struct proof-state (tele output)
    #:transparent)

  (define/contract (complete-proof? st)
    (-> proof-state? boolean?)
    (zero? (scope-valence (proof-state-output st))))

  (define/contract (proof-extract st)
    (-> complete-proof? bind?)
    (instantiate (proof-state-output st) '()))

  (define/contract (unpack-proof-state state)
    (-> proof-state? (values ctx? bind?))
    (match-define (proof-state tele output) state)
    (define xs (map (λ (g) (fresh)) tele))
    (values
     (telescope->ctx xs tele)
     (instantiate output xs)))

  (define (pack-proof-state subgoals output)
    (let ([xs (map car subgoals)])
      (proof-state (ctx->telescope subgoals) (abstract xs output))))

  (define-syntax (subgoals stx)
    (syntax-parse stx
      [(_ ((X:id goal:expr) ...) o:expr)
       (syntax/loc stx
         (proof-state
          (telescope (X goal) ...)
          (in-scope (X ...) o)))]))

  (define/contract (pack-goal ctx rty)
    (-> ctx? sort? >>?)
    (let ([xs (map car ctx)])
      (make->> xs (make-arity (ctx->telescope ctx) (abstract xs rty)))))

  (define/contract (unpack-goal goal)
    (-> >>? (values ctx? sort?))
    (define xs (>>-names goal))
    (define ty (>>-ty goal))
    (values (telescope->ctx xs (arity-domain ty)) (instantiate (arity-codomain ty) xs)))

  (define-match-expander >>
    (λ (stx)
      (syntax-parse stx
        [(_ Γ rty)
         (syntax/loc stx
           (app unpack-goal Γ rty))]))
    (λ (stx)
      (syntax-parse stx
        [(_ Γ rty)
         (syntax/loc stx
           (pack-goal Γ rty))])))

  (define-match-expander >:
    (λ (stx)
      (syntax-parse stx
        [(_ Ψ o)
         (syntax/loc stx
           (app unpack-proof-state Ψ o))]))
    (λ (stx)
      (syntax-parse stx
        [(_ Ψ o)
         (syntax/loc stx
           (pack-proof-state Ψ o))]))))

(require 'sequent)


(define/contract (eta cell)
  (-> (cons/c free-name? arity?) bind?)
  (match cell
    [(cons x (and (app arity-domain tele) (app arity-codomain cod)))
     (let* ([xs (map (λ (sc) (fresh)) tele)]
            [ctx (telescope->ctx xs tele)])
       (make-bind
        (abstract xs (make-plug x (map eta ctx)))))]))

(define/contract (plug* x Γ)
  (-> free-name? ctx? plug?)
  (make-plug x (map eta Γ)))

(define/contract (bind* Γ e)
  (-> ctx? any/c bind?)
  (define xs (map car Γ))
  (make-bind (abstract xs e)))


(struct exn:fail:refinement exn:fail (goal)
  #:transparent
  #:extra-constructor-name make-exn:fail:refinement)

(define (raise-refinement-error msg goal)
  (raise (exn:fail:refinement msg (current-continuation-marks) goal)))

(define-syntax (define-rule stx)
  (define (get-name h)
    (syntax-parse h
      [n:id #'n]
      [(h* e ...) (get-name #'h*)]))
  (syntax-parse stx
    [(_ head goal definition:expr ... ((x:id subgoal) ...) extract)
     (with-syntax ([rule-name (get-name #'head)])
       (syntax/loc stx
         (define head
           (contract
            tac/c
            (procedure-rename
             (λ (g)
               (match g
                 [(and (>> Γ J) goal)
                  definition ...
                  (subgoals ((x subgoal) ...) (bind* Γ extract))]
                 [other-goal
                  (raise-refinement-error (format "Inapplicable: ~a" other-goal) other-goal)]))
             'rule-name)
            'rule-name 'caller))))]))

(define tac/c
  (-> >>? proof-state?))

(define/contract id-tac
  tac/c
  (λ (goal)
    (subgoals
     ((X goal))
     (eta (cons X (>>-ty goal))))))

; Analogous to the THENL tactical
(define/contract (multicut t1 . ts)
  (->* (tac/c)
       #:rest (listof tac/c)
       tac/c)
  (define (multicut/aux subgoals tactics output subgoals-out env-out)
    (match* (subgoals tactics)
      [('() _)
       (>: subgoals-out (instantiate output env-out))]
      [((cons goal subgoals) (cons tactic tactics))
       (match-let ([(>: subgoals1 output1) (tactic (instantiate goal env-out))])
         (multicut/aux
          subgoals
          tactics
          output
          (append subgoals-out subgoals1)
          (append env-out (list output1))))]
      [(_ _) (error "Subgoals and tactics must be of same length") ]))

  (define (balance-tactics subgoals tactics)
    (match* (subgoals tactics)
      [('() _) '()]
      [((cons goal subgoals) '())
       (cons id-tac (balance-tactics subgoals '()))]
      [((cons goal subgoals) (cons tactic tactics))
       (cons tactic (balance-tactics subgoals tactics))]))

  (λ (goal)
    (match-let ([(proof-state subgoals output) (t1 goal)])
      (multicut/aux
       subgoals
       (balance-tactics subgoals ts)
       output
       '()
       '()))))

(define (orelse t1 . ts)
  (match ts
    ['() t1]
    [(cons t ts)
     (λ (goal)
       (with-handlers
           ([exn:fail:refinement?
             (λ (e)
               ((apply orelse (cons t ts)) goal))])
         (t1 goal)))]))


(define/contract ((probe-at loc) goal)
  (-> source-location? tac/c)
  (printf "~a: ~a" (source-location->string loc) goal)
  (subgoals
   ([X goal])
   (eta `(,X . ,(>>-ty goal)))))

(define-syntax (probe stx)
  (syntax-parse stx
    #:literals (probe)
    [probe
     (with-syntax
         ([source (source-location-source stx)]
          [line (source-location-line stx)]
          [col (source-location-column stx)]
          [pos (source-location-position stx)]
          [span (source-location-span stx)])
       (syntax/loc stx
         (probe-at (make-srcloc 'source 'line 'col 'pos 'span))))]))

(module+ test
  (define-signature L
    (prop () (SORT))

    (tm () (SORT))

    (conj
     ([p (arity () (prop))]
      [q (arity () (prop))])
     (prop))

    (disj
     ([p (arity () (prop))]
      [q (arity () (prop))])
     (prop))

    (imp
     ([p (arity () (prop))]
      [q (arity () (prop))])
     (prop))

    (T () (prop))

    (F () (prop))

    (nil () (tm))

    (pair
     ([m (arity () (tm))]
      [n (arity () (tm))])
     (tm))

    (fst
     ([m (arity () (tm))])
     (tm))

    (snd
     ([m (arity () (tm))])
     (tm))

    (inl
     ([m (arity () (tm))])
     (tm))

    (inr
     ([m (arity () (tm))])
     (tm))

    (split
     ([m (arity () (tm))]
      [l (arity ([x (tm)]) (tm))]
      [r (arity ([y (tm)]) (tm))]) ; for some reason, I can't use 'x' here. something about duplicate attributes
     (tm))

    (lam
     ([m (arity ([x (tm)]) (tm))])
     (tm))

    (is-true
     ([p (arity () (prop))])
     (SORT)))


  (define-rule (hyp x)
    (>> (with-hyp Γ0 x () tyx Γ1)
        goalTy)
    (if (not (equal? goalTy tyx))
        (raise-refinement-error
         (format "Hypothesis mismatch ~a has type ~a, but expected ~a" x tyx goalTy)
         goalTy)
        '())
    ()
    x)

  (define-rule conj/R
    (>> Γ (is-true (conj p q)))
    ([X (>> Γ (is-true p))]
     [Y (>> Γ (is-true q))])
    (pair (plug* X Γ) (plug* Y Γ)))

  (define-rule (conj/L x x0 x1)
    (>> (with-hyp Γ0 x () (is-true (conj p q)) Γ1)
        (is-true (unapply r x)))
    (define Γ/pq
      (splice-context
       Γ0
       ([x0 (is-true p)] [x1 (is-true q)])
       (Γ1 (pair x0 x1))))
    ([X (>> Γ/pq (is-true (r (pair x0 x1))))])
    (subst
     ([x0 () (fst x)]
      [x1 () (snd x)])
     (plug* X Γ/pq)))

  (define-rule disj/R/1
    (>> Γ (is-true (disj p q)))
    ([X (>> Γ (is-true p))])
    (inl (plug* X Γ)))

  (define-rule disj/R/2
    (>> Γ (is-true (disj p q)))
    ([X (>> Γ (is-true q))])
    (inr (plug* X Γ)))

  (define-rule (disj/L x)
    (>> (with-hyp Γ0 x () (is-true (disj p q)) Γ1)
        (is-true (unapply r x)))
    (define (Γ/p y) (splice-context Γ0 ([y (is-true p)]) (Γ1 (inl y))))
    (define (Γ/q y) (splice-context Γ0 ([y (is-true q)]) (Γ1 (inr y))))
    ([L (>> (Γ/p x) (is-true (r (inl x))))]
     [R (>> (Γ/q x) (is-true (r (inr x))))])
    (split x (xl) (plug* L (Γ/p xl)) (xr) (plug* R (Γ/q xr))))


  (define-rule (imp/R x)
    (>> Γ (is-true (imp p q)))
    (define (Γ/p x)
      (ctx-set Γ x (is-true p)))
    ([X (>> (Γ/p x) (is-true q))])
    (lam (x) (plug* X (Γ/p x))))

  (define-rule T/R
    (>> Γ (is-true (T)))
    ()
    (nil))

  (define-rule (F/L x)
    (>> (with-hyp Γ0 x () (is-true (F)) Γ1)
        (is-true p))
    ()
    (nil))

  (define-syntax (lam/t stx)
    (syntax-parse stx
      [(_ (x:id) t:expr)
       (with-syntax
           ([var-name (symbol->string (syntax->datum #'x))])
         (syntax/loc stx
           (let ([x (fresh var-name)])
             (multicut (imp/R x) t))))]))


  (define/contract (split/t x t1 t2)
    (-> free-name? tac/c tac/c
        tac/c)
    (multicut
     (disj/L x)
     t1
     t2))

  (define/contract (pair/t t1 t2)
    (-> tac/c tac/c
        tac/c)
    (multicut
     conj/R
     t1
     t2))


  (require (only-in racket/port with-output-to-string))
  (check-not-false
   (regexp-match
    ;; This is a hacky regexp that should match a source location, but changes to
    ;; the printing of various structs or source locations may invalidate it.
    ;; The idea is that a probe should have run while executing the test, but
    ;; we can't predict the filename or the gensym used for printing the internal
    ;; names of the >>.
    #rx"refinement-engine\\.rkt:[0-9]+.[0-9]+: #\\(struct:>> \\([^)]+\\)"
    (with-output-to-string
     (λ ()
       (check-equal?
        (let* ([goal (>> '() (is-true (imp (disj (T) (F)) (conj (T) (T)))))]
               [script
                (lam/t (x)
                       (multicut
                        probe
                        (split/t x (pair/t (hyp x) T/R) (orelse T/R (F/L x)))))])
          (proof-extract (script goal)))
        (bind ()
              (lam (x)
                   (split x
                          (b) (pair b (nil))
                          (b) (nil))))))))))
