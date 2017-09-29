#lang rosette

(define-symbolic b boolean?)

(define x 0) ; x is concrete Int

x ; concrete

;; mutating x in symbolic path changes it to symbolic
(if b
    (set! x 10)
    (set! x 11))

x ; symbolic
