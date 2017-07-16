#lang scribble/manual
@require[scribble/bnf scriblib/footnote]
@require[@for-label[grit
                    racket/base
                    racket/contract]]

@title{grit}
@author{David Christiansen and Jon Sterling}

@defmodule[grit]

This is an implementation of a variant of the Edinburgh Logical Framework, namely Jason Reed's @bold{Tiny LF}. Tiny LF is a further development of Canonical LF to have a more rigid and syntactic notion of type suitable for use as a syntactic framework, along the lines of dependently-sorted abstract syntax. Moreover, Tiny LF eschews the classic distinction between signature and context.

@BNF[
 (list
  @nonterm{arity}
  @BNF-seq[@litchar{(arity} @nonterm{telescope} @nonterm{sort}@litchar{)}])
 (list
  @nonterm{telescope}
  @BNF-seq[@litchar{(}@kleenestar[@BNF-seq[@litchar{[} @nonterm{id} @nonterm{arity} @litchar{]}]]@litchar{)}])
 (list
  @nonterm{sort}
  @litchar{(SORT)}
  @nonterm{atomic-term})
 (list
  @nonterm{atomic-term}
  @BNF-seq[@litchar{(plug}@nonterm{id} @nonterm{spine} @litchar{)}])
 (list
  @nonterm{spine}
  @kleenestar[@nonterm{term}])
 (list
  @nonterm{term}
  @BNF-seq[@litchar{(bind} @litchar{(}@kleenestar[@nonterm{id}]@litchar{)} @nonterm{atomic-term}@litchar{)}])]

The syntax is divided into @emph{arities} (dependent function types), @emph{sorts}, @emph{terms} (lambda abstractions) and @emph{atomic terms}.

@section{Syntax}

@defproc[(SORT) ?rtype]{
 The sort of sorts.
}

@defform[(arity ([id ar] ...) tau) #:contracts ([ar arity?] [tau sort?])]{
 Constructs an arity from a telescope and a sort which has the variables of the telescope bound.
}

@defform[(bind (id ...) r) #:contracts ([r atomic-term?])]{
 Constructs a term, binding a list of identifiers in an atomic term.
}

@defform[(plug x m ...) #:contracts ([x free-name?] [m term?])]{
 Constructs an application expression (atomic term) from a free variable and a spine of terms.
}

@section{Typechecking}

@defproc[(check-arity [ctx ctx?] [ar arity?]) any/c]{
 Checks whether an arity is valid relative to context @racket[ctx].
}

@defproc[(check-sort [ctx ctx?] [tau sort?]) any/c]{
 Checks whether a sort is valid relative to context @racket[ctx].
}

@defproc[(infer-atomic-term [ctx ctx?] [r atomic-term?]) sort?]{
 Infers the sort of an atomic term @racket[r] relative to context @racket[ctx].
}

@defproc[(check-atomic-term [ctx ctx?] [r atomic-term?] [tau sort?]) any/c]{
 Checks whether an atomic term @racket[r] has sort @racket[tau] relative to @racket[ctx].
}

@defproc[(check-term [ctx ctx?] [m term?] [ar arity?]) any/c]{
 Checks whether a term expression @racket[m] has arity @racket[ar] relative to @racket[ctx].
}

@section{How grit works}

Grit, internally, uses a lot of racket magic that makes it very nice to use, but somewhat challenging to understand. Let's look at an example language definition and what happens under the hood. The language we'll consider is the simply-typed lambda calculus, with just the unit base type. This isn't the best use of grit, but it's simple enough that the details will be clear in the internals.

@subsection{Signatures}

At its core, grit is built around pattern matching. We'll see what that means. First, the signature of our language:

@racketblock[
(define-signature STLC
  (tm () (SORT))
  (tp () (SORT))

  (lam
    ([m (arity ([x (tm)]) (tm))])
    (tm))

  (app
    ([e1 (arity () (tm))]
      [e2 (arity () (tm))])
    (tm))

  (⋆ () (tm))

  (unit () (tp))
  (fun
    ([t1 (arity () (tp))]
      [t2 (arity () (tp))])
    (tp)))]

@racket[define-signature] is a macro. In this example, it expands into:

@racketblock[
(define STLC
  (signature
   (tm (arity () (SORT)))
   (tp (arity () (SORT)))
   (lam (arity ((m (arity ((x (tm))) (tm)))) (tm)))
   (app (arity ((e1 (arity () (tm))) (e2 (arity () (tm)))) (tm)))
   (⋆ (arity () (tm)))
   (unit (arity () (tp)))
   (fun (arity ((t1 (arity () (tp))) (t2 (arity () (tp)))) (tp)))))
(define-signature-helper tm ())
(define-signature-helper tp ())
(define-signature-helper lam ((m (arity ((x (tm))) (tm)))))
(define-signature-helper app ((e1 (arity () (tm))) (e2 (arity () (tm)))))
(define-signature-helper ⋆ ())
(define-signature-helper unit ())
(define-signature-helper fun ((t1 (arity () (tp))) (t2 (arity () (tp)))))
]

@racket[define-signature-helper] is also a macro, and defines its first argument as a match expander. This means that when that name (eg. ⋆) appears as the head of a pattern, some custom code will be run on that pattern to expand into a "real" pattern. Let's look at what the @racket[lam] @racket[define-signature-helper] expands into:

@racketblock[
(begin-for-syntax
    (define-values (help-pattern-expander)
      (new-lambda
       (stx)
       (syntax-parse
        stx
        [(_ (x) m)
         (with-syntax
          ([name-str (symbol->string (syntax->datum #'lam))])
          (syntax/loc stx (app unwrap-nullary-binder (plug (free-name 'lam name-str) (bind (x) m)))))]))))
   (begin-for-syntax
    (define-values (help-constructor-expander)
      (new-lambda
       (stx)
       (syntax-parse
        stx
        [(_ (x) m)
         (with-syntax
          ([name-str (symbol->string (syntax->datum #'lam))])
          (syntax/loc stx (plug (free-name 'lam name-str) (bind (x) m))))]))))
   (define-syntaxes (lam)
     (make-match-expander help-pattern-expander help-constructor-expander))]

Whoa, that's pretty crazy! Let's pick it apart. Really, it's just defining @racket[lam] as a match-expander, with @racket[help-pattern-expander] transforming its occurences inside a pattern and @racket[help-constructor-expander] transforming its occurences inside an expression. There's a bunch of macro stuff happening around it, but @racket[help-pattern-expander] takes some pattern that looks like:

@racketblock[(lam (x) m)]

and turns it into a real pattern using some of grit's internals:

@racketblock[(app unwrap-nullary-binder (plug (free-name 'lam "lam") (bind (x) m)))]

Note that @racket[app] as a pattern will apply the first expr to the value being matched against, and then use the remainder as a pattern to match against the value that returns. We'll see this in play soon.

That's what we match against, but when we write something like @racket[(lam (x) ⋆)], it gets expanded into @racket[(plug (free-name 'lam "lam") (bind (x) ⋆))]. Just what you'd expect — this is exactly what gets matched against!

The @racket[signature] from earlier is also a match expander. In both pattern and expression form, @racket[STLC] gets transformed into:

@racketblock[
(list
  (cons (free-name 'tm "tm") (SORT))
  (cons (free-name 'tp "tp") (SORT))
  (cons (free-name 'lam "lam") ([m (arity ([x (tm)]) (tm))]) (tm))
  ...)]

It's just a list of pairs of what was originally written, with the name replaced by a @racket[free-name]. @note{You might see something else printed if you try to run STLC at the REPL. That's due to some weirdness with how grit prints things. It's the internal view of what you wrote.}

@subsection{Judgments and Rules}

We defined the syntax of terms and types. Now it's time to write down how to show that a term has a type. First, we'll define a signature for our typing judgment:

@racketblock[
(define-signature Jdg
  (truth () (SORT))
  (axiom () (truth))

  (has-type
   ([e (arity () (tm))]
    [t (arity () (tp))])
   (truth)))
]

We introduce a new sort, @racket[truth], to express the sort of judgment that @racket[has-type] is. We also define one way to form a truth. It's suggestively called @racket[axiom]. Now we can write down our typing rules. Here's one rule:

@racketblock[
(define-rule star-unit
  (>> Γ (has-type (⋆) (unit)))
  ()
  (axiom) ; ??? what is this called
  )]

First, we give the name of the rule: @racket[star-unit]. Next, we have a sequent. @racket[>>] should be interpreted as ⊢. The Γ immediately after @racket[>>] is a context. After that, we have a list of expressions. In this rule, we only have one expression, and it says that ⋆ has type unit. After that first sequent, we have a list of subgoals. In this rule it is empty. We'll soon see what it means. Finally, we have the ???.

Here's the one other rule in our system: