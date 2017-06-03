#lang scribble/manual
@require[scribble/bnf]
@require[@for-label[racket-logical-framework
                    racket/base
                    racket/contract]]

@title{racket-logical-framework}
@author{David Christiansen and Jon Sterling}

@defmodule[racket-logical-framework]

This is an implementation of a variant of the Edinburgh Logical Framework, namely Jason Reed's @bold{Tiny LF}.
 Tiny LF is a further development of Canonical LF to have a more rigid and syntactic notion of type suitable for use as a syntactic framework, along the lines of dependently-sorted abstract syntax. The logical framework has the following grammar:

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

@defproc[(TYPE) ?rtype]{
 The atomic type of types.
}