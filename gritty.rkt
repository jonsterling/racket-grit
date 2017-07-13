#lang racket

(require "locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt")
(require syntax/srcloc)

(module+ test (require rackunit))

;; Proofs output feedback
(struct goal-feedback (loc goal solved?) #:transparent)

(define (feedback? x)
  (goal-feedback? x))

;; A complete module development
(struct module-node (defs) #:transparent)
;; A top-level definition
(struct def-node (name goal body loc goal-loc) #:transparent)
;; A shed node that records incomplete input
(struct shed-node (text loc) #:transparent)

(define current-proof-namespace
  (make-parameter (current-namespace)))

(define/contract (interpret-mod m)
  (-> module-node? (listof feedback?))
  (match m
    [(module-node defs)
     (interpret-defs defs)]))



(define/contract (interpret-defs ds)
  (-> (listof def-node?) (listof feedback?))
  (match ds
    ['() '()]
    [(cons one-def more-defs)
     (let-values ([(feedback lem) (interpret-def one-def)])
       (append feedback (interpret-defs  more-defs)))]))




(define/contract (interpret-def d)
  (->  def-node? (values (listof feedback?) #f))
  (match-let ([(def-node name goal body loc goal-loc) d])
    (let ([goal-val
           (with-input-from-string goal
             (thunk (eval (read) (current-proof-namespace))))])
      (if (not (eval `(>>? ,goal-val) (current-proof-namespace)))
          (error (format "Not a goal: ~a" goal-val))
          (let-values ([(feedback ext) (interpret-step goal-val body)])
            (values feedback
                    #f))))))

(define/contract (interpret-step goal s)
  (-> >>?
      shed-node?
      (values (listof feedback?)
              (or/c #f bind?)))
  (cond
    [(shed-node? s) (values (list (goal-feedback (shed-node-loc s) goal #f)) #f)]
    [else (error "Invalid node")]))


(module goals racket/base
  (require racket/match "locally-nameless.rkt")
  ;; A presentation goal is a proof goal that is either boring (to be
  ;; solved by automation) or a genuine problem (to be solved by human
  ;; refinement)
  (struct presentation-goal (goal)
    #:transparent
    #:property prop:bindings
    (bindings-support
     (λ (pg frees i)
       (match-define (presentation-goal g) pg)
       (match-define (bindings-support abs _) (bindings-accessor g))
       ((if (problem? pg) problem boring)
        (abs g frees i)))
     (λ (pg i new-exprs)
       (match-define (presentation-goal g) pg)
       (match-define (bindings-support _ inst) (bindings-accessor g))
       ((if (problem? pg) problem boring)
        (inst g i new-exprs)))))
  (struct problem presentation-goal () #:transparent)
  (struct boring presentation-goal () #:transparent)
  (provide (struct-out problem) (struct-out boring) presentation-goal?))
(require 'goals)


(module+ test
  (module proof-module racket
    (require "refiner-demo.rkt")
    (provide here)
    (define-namespace-anchor here))
  (require 'proof-module)
  (current-proof-namespace (namespace-anchor->namespace here))


  (define-simple-check (check-goal-feedback? x)
    (goal-feedback? x))

  (define test-gritty-proof-1
    (def-node "prf"
      "(>> '() (is-true (conj (disj (T) (F)) (conj (T) (T)))))"
      (shed-node "stuff" #'here)
      #'here1
      #'here2))

  (define-values (out-1 lem) (interpret-def test-gritty-proof-1))
  (check-equal? (length out-1) 1)
  (check-goal-feedback? (car out-1)))
