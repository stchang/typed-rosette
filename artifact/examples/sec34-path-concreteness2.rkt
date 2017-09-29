#lang typed/rosette

(define y : Int 0)  ; y is possibly symbolic Int

;; ok, since y is symbolic, so ok to call f in either symbolic or concrete path
(define (f [z : CInt]) -> CUnit
  (set! y z))

(f 10)
y

(define-symbolic b boolean?)
(if b (f 1) (f 2)) ; ok since y is possibly symbolic
y

(define x : CInt 0) ; x is concrete Int

;; type err, since it is not valid to call f in both concrete and symbolic path
;; uncomment to see type error
#;(define (g [z : CInt]) -> CUnit
  (set! x z))
