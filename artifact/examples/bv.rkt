#lang typed/bv

(bv 1 4) ; constructs bitvector with value 1 and length 4
(define-symbolic x : Int)
(bv x 4) ; type err
