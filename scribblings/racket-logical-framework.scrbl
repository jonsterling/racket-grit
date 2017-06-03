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
  @nonterm{type}
  @BNF-seq[@litchar{Π} @nonterm{tele} @nonterm{rtype}])
 (list
  @nonterm{tele}
  @kleenestar[@BNF-seq[@litchar{(} @nonterm{id} @litchar{:} @nonterm{type} @litchar{)}]])
 (list
  @nonterm{rtype}
  @litchar{TYPE}
  @nonterm{rtm})
 (list
  @nonterm{rtm}
  @BNF-seq[@nonterm{id} @litchar{[} @nonterm{spine} @litchar{]}])
 (list
  @nonterm{spine}
  @kleenestar[@nonterm{ntm}])
 (list
  @nonterm{ntm}
  @BNF-seq[@nonterm{Λ} @kleenestar[@nonterm{id}] @nonterm{rtm}])]

The syntax is divided into @emph{proper types} (dependent function types), @emph{atomic types}, @emph{normal terms} (lambda abstractions) and @emph{atomic terms}.

@section{Syntax}

@defproc[(TYPE) ?rtype]{
 The atomic type of types.
}

@defform[(Π ((id type) ...) rty) #:contracts ([type Π?] [rty rtype?])]{
 Constructs a dependent function type from a telescope and an atomic type which has the variables of the telescope bound.
}

@defform[(Λ (id ...) rtm) #:contracts ([rtm $?])]{
 Constructs a lambda abstraction (normal term) from a list of identifiers, and an atomic term which has those identifiers bound.
}

@defform[($ x ntm ...) #:contracts ([x free-name?] [ntm Λ?])]{
 Constructs an application expression (atomic term) from a free variable and a spine of normal terms.
}

@section{Typechecking}

@defproc[(chk-type [ctx ctx?] [ty Π?]) any/c]{
 Checks whether a proper type expression is valid relative to context @racket[ctx].
}

@defproc[(chk-rtype [ctx ctx?] [rty rtype?]) any/c]{
 Checks whether an atomic type expression is valid relative to context @racket[ctx].
}

@defproc[(inf-rtm [ctx ctx?] [rtm $?]) rtype?]{
 Infers the type of an atomic type expression @racket[rtm] relative to context @racket[ctx].
}

@defproc[(chk-rtm [ctx ctx?] [rtm $?] [rty rtype?]) any/c]{
 Checks whether an atomic term expression @racket[rtm] has atomic type @racket[rty] relative to @racket[ctx].
}

@defproc[(chk-ntm [ctx ctx?] [ntm Λ?] [ty Π?]) any/c]{
 Checks whether a normal term expression @racket[ntm] has proper type @racket[ty] relative to @racket[ctx].
}