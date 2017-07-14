#lang racket/gui
(require "locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt")
(require "gritty.rkt")

;;; MVC boilerplate
(define observable<%>
  (interface ()
    (register! (->m any/c void?))
    (notify-observers (->m void?))))

(define observer<%>
  (interface ()
    (notify-updated (->m (is-a?/c observable<%>) void?))))

(define observable-mixin
  (mixin () (observable<%>)
    (super-new)
    (define listeners (weak-seteq))

    (define/public (notify-observers)
      (for ([l listeners])
        (send l notify-updated this)))

    (define/public (register! l)
      (set-add! listeners l))))


;;; Model
(define proof-step<%>
  (interface (observable<%>)
    [get-tactic-text (->m string?)]
    [set-tactic-text (->m string? void?)]
    [get-goal (->m any/c)]
    [set-goal (->m any/c void?)]))

(define proof<%>
  (interface (observable<%>)
    [get-name (->m string?)]
    [get-goal (->m any/c)]
    [get-step (->m (is-a?/c proof-step<%>))]
    [set-step (->m (is-a?/c proof-step<%>) void?)]))

(define proof%
  (class* (observable-mixin object%) (proof<%>)
    (super-new)
    (init name goal step)
    (define n name)
    (define g goal)
    (define s step)

    (define/public (get-name)
      n)
    (define/public (get-goal)
      g)
    (define/public (get-step)
      s)
    (define/public (set-step new-s)
      (set! s new-s)
      (void))))



(define proof-step-mixin
  (mixin (observable<%>) (proof-step<%>)
    (super-new)
     (init-field goal
                 [tactic-text ""])

     (define/public (get-tactic-text)
       tactic-text)

     (define/public (set-tactic-text new-text)
       (set! tactic-text new-text)
       (send this notify-observers))

     (define/public (get-goal) goal)
     (define/public (set-goal new-goal)
       (set! goal new-goal)
       (send this notify-observers))))

(define shed%
  (proof-step-mixin
   (observable-mixin
    (class object% (super-new)))))

(define has-subgoals<%>
  (interface ()
    [get-subgoals (->m (listof (is-a?/c proof-step<%>)))]
    [set-subgoals (->m (listof (is-a?/c proof-step<%>)) void?)]))

(define by%
  (proof-step-mixin
   (observable-mixin
    (class* object% (has-subgoals<%>)
      (super-new)
      (init-field subgoals)

      (define/public (get-subgoals)
        subgoals)
      (define/public (set-subgoals goals)
        (set! subgoals goals)
        (send this notify-observers))))))

(define status/c
  (or/c 'complete 'refined 'incomplete (list/c 'mistake exn:fail?)))

;;; Saving and loading
(define/contract (gritty-module->model mod)
  (-> module-node? (is-a?/c proof-step<%>))
  (match mod
    [(module-node (list d))
     (gritty-def->model d)]
    [_ (error 'todo)]))

(define/contract (gritty-def->model def)
  (-> def-node? (is-a?/c proof<%>))
  (match def
    [(def-node name goal body _ _)
     (error 'todo)]))

(define/contract (gritty-step->model proof)
  (-> (or/c by-node? shed-node?) (is-a?/c proof-step<%>))
  (match proof
    [(shed-node text _) (new shed% [tactic-text text])]))

;;; Presentations
(define proof-view%
  (class vertical-panel%
    (super-new)
    (init-field proof)
    (define row1 (new horizontal-panel% [parent this] [stretchable-height #f]))
    (define name-and-goal
      (new message% [parent row1] [label (format "~a : ~a"
                                                 (send proof get-name)
                                                  (send proof get-goal))]))
    (define row2 (new vertical-panel% [parent this] [style '(auto-vscroll)]))
    (define p (new step-view% [parent row2] [step (send proof get-step)]))))

(define step-view%
  (class vertical-panel%
    (super-new [stretchable-height #f])
    (init-field step)

    (define inner (new horizontal-panel% [parent this]))

    (define children
      (if (is-a? step has-subgoals<%>)
          (for/list ([sub (in-list (send step get-subgoals))])
            (define goal-box
              (new horizontal-panel% [parent this] [stretchable-height #f]))
            (define spacer
              (new panel%
                   [parent goal-box]
                   [stretchable-width #f]
                   [stretchable-height #f]
                   [min-height 10]
                   [min-width 40]))
            (new step-view%
                 [parent goal-box]
                 [step sub]))
          '()))

    (define goal-view
      (new message%
           [parent inner]
           [label "Goal"]))

    (define contents
      (new text-field%
           [parent inner]
           [label "By"]
           [callback (lambda (me event)
                       (send step set-tactic-text (send me get-value)))]))

    (define/public (notify-updated x)
      (send goal-view set-label (format "~a" (send x get-goal)))
      (send contents set-value (send x get-tactic-text)))

    (send step register! this)
    (notify-updated step)))

(define (prover-namespace logic-module)
  (define ns (make-base-namespace))
  (for ([mod '("locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt")])
    (namespace-attach-module (current-namespace) mod ns))
  (parameterize ([current-namespace ns])
    (for ([mod '("locally-nameless.rkt" "logical-framework.rkt" "refinement-engine.rkt")])
      (namespace-require mod))
    ;; Finally load the user's logic module
    (namespace-require logic-module))
  ns)

;; The argument ns is the namespace in which to interpret statements
;; and tactics
(define (prover-frame ns)
  ;; Model
  (define st (new by%
                  [goal #t]
                  [tactic-text "whoa"]
                  [subgoals (list (new shed%
                                       [goal #f]
                                       [tactic-text "hi"])
                                  (new shed%
                                       [goal 'foo]
                                       [tactic-text "again"]))]))

  (define p (new proof% [name "Test"] [goal "Something"] [step st]))

  ;; Presentations
  (define f (new frame% [label "Gritty"]))
  (define proof (new proof-view% [parent f] [proof p]))


  (send f show #t)

  (define f2 (new frame% [label "Gritty"]))
  (define proof2 (new proof-view% [parent f2] [proof p]))


  (send f2 show #t))
