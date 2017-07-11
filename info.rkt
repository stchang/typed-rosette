#lang info

(define collection 'multi)

(define deps
  '(("racket" #:version "6.8.0.3")
    "base"
    "rosette"
    "turnstile"
    "rackunit-lib"
    "lens-common"
    "lens-unstable"
    "syntax-classes-lib"
    ))

(define build-deps
  '("rackunit-lib"))
