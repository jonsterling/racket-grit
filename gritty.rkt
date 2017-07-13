#lang racket

(module logic racket/base
  (struct >> (hypotheses goal))
  (provide (struct-out >>)))
(require 'logic)


(module+ test
  (module proof-module racket
    (require (submod ".."  ".." logic))
    (provide here)
    (define-namespace-anchor here))

  (require 'proof-module)
  (with-input-from-string "(>> '() (void))"
    (thunk (eval (read) (namespace-anchor->namespace here)))))
