#lang info

(define test-timeouts
  '(("bv-ref-tests.rkt" 300)
    ("ifc-tests.rkt" 300)))

(define compile-omit-paths '("tmp"))

(define test-omit-paths '("tmp"))
