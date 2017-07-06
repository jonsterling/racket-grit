#lang scribble/manual
@require[scribble/bnf]
@require[@for-label[racket-logical-framework
                    racket/base
                    racket/contract]]

@title{racket-logical-framework}
@author{David Christiansen and Jon Sterling}

@defmodule[racket-logical-framework]

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