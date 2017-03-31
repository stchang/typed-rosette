#lang racket/base
(require "struct-tests.rkt" rackunit)

;; test Typed Rosette properly preserves access to struct-info of "a"
(struct b a (y))
;; todo: add checks when typed code imported into untyped code
(check-true (b? (b 1 2)))
