#lang racket/gui
(require (prefix-in nom: "locally-nameless.rkt"))
(require "logical-framework.rkt" "refinement-engine.rkt")
(require "gritty.rkt")

;;; Small helpers

(define (as-label-string str)
  (if (string? str)
      (if (> (string-length str) 200)
          (string-append (substring str 0 (min (string-length str) 197)) "...")
          str)
      (as-label-string (format "~a" str))))

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
  (or/c 'pending
        (list/c 'complete any/c) ;; the extract
        (list/c 'refined exact-nonnegative-integer? exact-nonnegative-integer?)
        'incomplete
        'unreachable
        (list/c 'mistake exn:fail?)))

(define proof-step<%>
  (interface (observable<%>)
    [get-parent (->m (or/c (recursive-contract (is-a?/c proof-step<%>)) #f))]
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
                [parent #f]
                [tactic-text ""])

    (inherit notify-observers)

    (define current-status 'incomplete)
    (define internal-name (nom:fresh))

    (define/public (get-parent) parent)

    (define/public (get-subgoals)
      subgoals)
    (define/public (set-subgoals goals)
      (set! subgoals goals)
      (send this notify-observers))
    (define/public (get-tactic-text)
      tactic-text)

    (define/public (get-status)
      current-status)

    (define/public (get-extract)
      (match current-status
        [`(complete ,ext) ext]
        [_ internal-name]))

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
              (let loop ([steps-out '()]
                         [steps-in (get-subgoals)]
                         [remaining-subgoals subgoals])
                (match* (steps-in remaining-subgoals)
                  [(_ (list)) (reverse steps-out)]
                  [((list) (cons g gs))
                   (loop (cons (new by%
                                    [goal (nom:instantiate g (for/list ([prev (reverse steps-out)])
                                                               (send prev get-extract)))]
                                    [subgoals '()]
                                    [parent this])
                               steps-out)
                         '()
                         gs)]
                  [((cons s ss) (cons g gs))
                   (send s set-goal (nom:instantiate g (for/list ([prev (reverse steps-out)])
                                                         (send prev get-extract))))
                   (loop (cons s steps-out)
                         ss
                         gs)])))
             (set-subgoals subs)
             (if (pair? subs)
                 (set-status `(refined 0 ,(length subs)))
                 (set-status `(complete ,(nom:instantiate ext '())))))]))
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
        [`(complete ,_)
         (new message% [parent this] [label "✔"])]
        [`(refined ,i ,j)
         (new message% [parent this] [label (format "~a/~a" i j)])]
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
    (init step)
    (init [indent? #t])

    (define the-step step)

    (define/public (set-step! new-step)
      (send the-step unregister! this)
      (set! the-step new-step)
      (send the-step register! this)
      (notify-updated new-step))

    (define inner
      (new horizontal-panel% [parent this]))
    (define children-container
      (if indent?
          (let* ([h (new horizontal-panel% [parent this])]
                 [s (new horizontal-panel%
                         [parent h]
                         [stretchable-width #f]
                         [stretchable-height #f]
                         [min-height 10]
                         [min-width 40])]
                 [v (new vertical-panel% [parent h])])
            v)
          (new vertical-panel% [parent this])))

    (define (update-children)
      (when (is-a? the-step has-subgoals<%>)
        (send children-container change-children
              (lambda (old-children)
                (let loop ([subgoals (send the-step get-subgoals)]
                           [widgets old-children]
                           [to-show '()])
                  (match* (subgoals widgets)
                    [((list) ws) (reverse to-show)]
                    [((cons g gs) (list))
                     (loop gs '() (cons (new step-view%
                                             [parent children-container]
                                             [step g]
                                             [indent? #t])
                                        to-show))]
                    [((cons g gs) (cons w ws))
                     (send w set-step! g)
                     (loop gs ws (cons w to-show))]))))))

    (define status-view
      (new status-view% [parent inner] [status 'incomplete]))

    (define goal-view
      (new message%
           [parent inner]
           [label "Uninitialized Goal"]
           [auto-resize #t]))

    (define contents
      (new text-field%
           [parent inner]
           [label "By"]
           [callback (lambda (me event)
                       (send the-step set-tactic-text (send me get-value)))]))

    (define (init-view x)
      (send status-view set-status (send x get-status))
      (send goal-view set-label (as-label-string (format "~a" (send x get-goal))))
      (send contents set-value (send x get-tactic-text)))

    (define/public (notify-updated x)
      (init-view x)
      (update-children))

    (send the-step register! this)
    (init-view the-step)))

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
                      [tactic-text ""]
                      [subgoals '()]))

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
