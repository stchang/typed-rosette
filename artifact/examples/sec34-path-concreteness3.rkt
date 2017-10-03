#lang typed/rosette

(define x : CInt 0) ; x is concrete Int

;; define/conc restricts g: may only be called in concrete path
;; - so g type checks
(define/conc (g [z : CInt]) -> CUnit
  (set! x z))

(g 10) ; ok, concrete path

(define-symbolic b boolean?)

(if b (g 1) (g 2)) ; type err: cannot call g in symbolic path
