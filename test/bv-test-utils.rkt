#lang racket/base
(require syntax/parse/define (for-syntax racket/base))
(require (prefix-in bv: "../sdsl/typed-bv/bv.rkt")
         turnstile/rackunit-typechecking)
(provide check-equal/rand/bv)

(define-simple-macro (check-equal/rand/bv f)
  #:with out (syntax/loc this-syntax 
               (check-equal/rand f
                #:process (bv:λ ([x : bv:CInt]) (bv:#%app bv:bv x))))
  out)
