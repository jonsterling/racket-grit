#lang scribble/manual
@require[@for-label[racket-logical-framework
                    racket/base
                    racket/contract]]

@title{racket-logical-framework}
@author{David Christiansen and Jon Sterling}

@defmodule[racket-logical-framework]

This is an implementation of a variant of the Edinburgh Logical Framework, namely Jason Reed's @bold{Tiny LF}.
 Tiny LF is a further development of Canonical LF to have a more rigid and syntactic notion of type suitable for use as a syntactic framework, along the lines of dependently-sorted abstract syntax.


