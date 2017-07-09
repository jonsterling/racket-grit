#lang racket

(require "logical-framework.rkt" "refinement-engine.rkt")

;; A complete module development
(struct module-node (defs) #:transparent)
;; A top-level definition
(struct def-node (name goal body loc) #:transparent)
;; A refined node in the proof. The text used to refine it is stored as a string, but it
;; will be subject to eval.
(struct by-node (text subs loc) #:transparent)
;; A shed node that records incomplete input
(struct shed-node (text loc) #:transparent)


;; Proofs output a series of annotations
(struct goal-annot (loc goal) #:transparent)
(struct mistake-annot (loc goal) #:transparent)
(struct extract-annot (loc goal) #:transparent)

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

(define/contract (mark-problem goal)
  tac/c
  (subgoals
   ((X (problem goal)))
   (eta (cons X (>>-ty goal)))))

(define/contract (mark-boring goal)
  tac/c
  (subgoals
   ((X (boring goal)))
   (eta (cons X (>>-ty goal)))))

(define/contract (tactic->presentation-tactic t)
  (-> tac/c tac/c)
  (then t mark-problem))


(module+ test
  (require "refiner-demo.rkt"))
