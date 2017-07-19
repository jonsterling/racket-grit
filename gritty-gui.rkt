#lang racket/gui
(require (prefix-in nom: "locally-nameless.rkt"))
(require "logical-framework.rkt" "refinement-engine.rkt")
(require "gritty.rkt")

;;; MVC boilerplate
(define observable<%>
  (interface ()
    (register! (->m any/c void?))
    (unregister! (->m any/c void?))
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
      (set-add! listeners l))

    (define/public (unregister! l)
      (set-remove! listeners l))))


;;; Model
(define status/c
  (or/c 'pending 'complete 'refined 'incomplete 'unreachable (list/c 'mistake exn:fail?)))

(define proof-step<%>
  (interface (observable<%>)
    [get-tactic-text (->m string?)]
    [set-tactic-text (->m string? void?)]
    [get-goal (->m any/c)]
    [set-goal (->m any/c void?)]
    [get-status (->m status/c)]))

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


(define has-subgoals<%>
  (interface ()
    [get-subgoals (->m (listof (is-a?/c proof-step<%>)))]
    [set-subgoals (->m (listof (is-a?/c proof-step<%>)) void?)]))

(define by%
  (class* (observable-mixin object%) (has-subgoals<%> proof-step<%>)
    (super-new)
    (init-field goal
                subgoals
                [tactic-text ""])

    (inherit notify-observers)

    (define current-status 'incomplete)

    (define/public (get-subgoals)
      subgoals)
    (define/public (set-subgoals goals)
      (set! subgoals goals)
      (send this notify-observers))
    (define/public (get-tactic-text)
      tactic-text)

    (define/public (get-status)
      current-status)

    (define (set-status new-status)
      (set! current-status new-status)
      (notify-observers))

    (define/public (set-tactic-text new-text)
      (set! tactic-text new-text)
      (notify-observers)
      (refine))

    (define (refine)
      (with-handlers ([exn:fail?
                          (lambda (e)
                            (set-status `(mistake ,e)))])
       (define tac-val
         (with-input-from-string (get-tactic-text)
           (thunk (eval (read) (current-proof-namespace)))))
        (match (tac-val (get-goal))
          [(proof-state subgoals ext)
           (set-status 'pending)
           (with-handlers ([exn:fail?
                          (lambda (e)
                            (set-status `(mistake ,e)))])
            (define subs
             (map cdr
              (let loop ([steps-out '()]
                         [steps-in (get-subgoals)]
                         [remaining-subgoals subgoals])
                (match* (steps-in remaining-subgoals)
                  [(_ (list)) (reverse steps-out)]
                  [((list) (cons g gs))
                   (define x (nom:fresh))
                   (loop (cons (cons x
                                     (new by%
                                          [goal (nom:instantiate g (map car (reverse steps-out)))]
                                          [subgoals '()]))
                               steps-out)
                         '()
                         gs)]
                  [((cons s ss) (cons g gs))
                   (send s set-goal (nom:instantiate g (map car (reverse steps-out))))
                   (define x (nom:fresh))
                   (loop (cons (cons x s) steps-out)
                         ss
                         gs)]))))
             (set-subgoals subs)
             (if (pair? subs)
                 (set-status 'refined)
                 (set-status 'complete)))]))
      (notify-observers))

    (define/public (get-goal) goal)
    (define/public (set-goal new-goal)
      (set! goal new-goal)
      (notify-observers))))

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
    [(shed-node text _) (new by% [tactic-text text] [subgoals '()])]))

;;; Presentations
(define status-view%
  (class horizontal-panel%
    (super-new [stretchable-width #f])
    (init-field status)
    (define/public (get-status)
      status)
    (define/public (set-status new-status)
      (set! status new-status)
      (update-view))

    (define (make-view s)
      (match s
        ['pending
         (new message% [parent this] [label "⏳"])]
        ['complete
         (new message% [parent this] [label "✔"])]
        ['refined
         (new message% [parent this] [label "⁇"])]
        ['incomplete
         (new message% [parent this] [label "⮕"])]
        ['unreachable
         (new message% [parent this] [label "☐"])]
        [`(mistake ,e)
         (define (show-mistake button event)
           (define mistake-frame (new frame% [label "Mistake"]  [width 700] [height 500]))
           (define text (new text%))
           (define canvas (new editor-canvas% [parent mistake-frame] [editor text]))
           (send text insert (format "~a" e) 0)
           (send mistake-frame show #t))
         (new button% [parent this] [label "❢"] [callback show-mistake])]))
    (define the-view (make-view status))
    (define (update-view)
      (send this change-children (thunk* '()))
      (set! the-view (make-view status)))))

(define proof-view%
  (class vertical-panel%
    (super-new)
    (init-field proof)
    (define row1
      (new horizontal-panel%
           [parent this]
           [stretchable-height #f]))
    (define name-and-goal
      (new message%
           [parent row1]
           [label (format "~a : ~a"
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

    (define status-view
      (new status-view% [parent inner] [status 'incomplete]))

    (define goal-view
      (new message%
           [parent inner]
           [label "Goal"]
           [auto-resize #t]))

    (define contents
      (new text-field%
           [parent inner]
           [label "By"]
           [callback (lambda (me event)
                       (send step set-tactic-text (send me get-value)))]))

    (define/public (notify-updated x)
      (send status-view set-status (send x get-status))
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
(define (prover-frame ns goal)
  (parameterize ([current-proof-namespace ns])
    ;; We need to create our own eventspace, because parameterizations
    ;; follow eventspace creation rather than object
    ;; instantiation. This means that if we want the namespace to show
    ;; up, we must have an eventspace inside the parameterization.
    (define es (make-eventspace))

    (define goal-val
      (with-input-from-string goal
        (thunk (eval (read) (current-proof-namespace)))))

    (parameterize ([current-eventspace es])
      ;; Model
      (define st (new by%
                      [goal goal-val]
                      [tactic-text "whoa"]
                      [subgoals (list (new by%
                                           [goal #f]
                                           [tactic-text "hi"]
                                           [subgoals '()])
                                      (new by%
                                           [goal 'foo]
                                           [tactic-text "again"]
                                           [subgoals '()]))]))

      (define p (new proof% [name "Test"] [goal goal-val] [step st]))

      ;; Presentations
      (define f (new frame% [label "Gritty"] [width 700] [height 500]))
      (define proof (new proof-view% [parent f] [proof p]))


      (send f show #t)

      (define f2 (new frame% [label "Gritty"]  [width 700] [height 500]))
      (define proof2 (new proof-view% [parent f2] [proof p]))

      (send f2 show #t))
    es))

(define (test-it)
  (prover-frame (prover-namespace "ctt.rkt") "(>> '() (is-inh (dsum (bool) (x) (bool-if x (unit) (void)))))"))

(module+ main (test-it))
