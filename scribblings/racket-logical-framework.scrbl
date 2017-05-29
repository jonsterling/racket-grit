#lang scribble/manual
@require[@for-label[racket-logical-framework
                    racket/base
                    racket/contract]]

@title{racket-logical-framework}
@author{David Christiansen and Jon Sterling}

@defmodule[racket-logical-framework]

This is an implementation of a variant of the Edinburgh Logical Framework, namely Jason Reed's @bold{Tiny LF}.
 Tiny LF is a further development of Canonical LF to have a more rigid and syntactic notion of type suitable for use as a syntactic framework, along the lines of dependently-sorted abstract syntax.

@section{Locally Nameless}

At the core of this library is an implementation of the @emph{Locally Nameless} scheme of variable binding based on Conor McBride's paper, @emph{I am not a Number---I am a Free Variable!}. (TODO: set up citations.)

@defstruct*[binder ([abs (-> any/c (listof free-name?) integer? any/c)]
                    [inst (-> any/c integer? (listof bindings?) any/c)])]{
 This is the signature of an object which is sensitive to binding. One function implements @emph{abstraction}, which is where a collection of free variables are closed over and replaced with indices; another function implements @emph{instantiation}, where bound variables are replaced with binding-sensitive expressions. This is a low-level interface which users will rarely have to implement, instead delegating to provided structures such as @racket[scope].
}

@defproc[(bindings? [v any/c]) boolean?]{
 Returns @racket[#t] if @racket[v] has the @racket[prop:bindings] property, @racket[#f] otherwise. This structure property is implemented in the following way:
 @racketblock[
 (struct my-struct (...)
   #:property prop:bindings
   (binder
    (λ (expr frees i) ...)
    (λ (expr i exprs) ...)))
 ]
}


(TODO: figure out why identifiers in the above codeblock aren't getting linked properly.)

