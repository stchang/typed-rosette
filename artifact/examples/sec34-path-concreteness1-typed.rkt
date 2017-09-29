#lang typed/rosette

(define-symbolic b boolean?)
(define x : CInt 0) ; x has type concrete Int

;; this is type err, due to symbolic path
;; o.w. x would change into symbolic value (with concrete type)
(if b
    (set! x 10)
    (set! x 11))
