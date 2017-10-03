#lang typed/rosette

;; EXAMPLE 1: annotation to allow mutation in symbolic path

(define-symbolic b : Bool)

; vector with concrete type; cannot mutate in symbolic path
(define v-conc (make-vector 7 #f))

;; uncomment to see type error
;(if b (vector-set! v-conc 0 #t) (vector-set! v-conc 1 #t))

;; add symbolic type annotation to allow mutation in symbolic path
(define v (make-vector 7 (ann #f : Bool)))

(if b (vector-set! v 0 #t) (vector-set! v 1 #t)) ; ok

v ; has one symbolic element at index 0



;; EXAMPLE 2: occurrence typing example

(define h (hash 'a 0 'b 1))

(let ([x (hash-ref h 'a #f)]) ; x has type (CU CInt CFalse)
;  (+ x 1) ;; type check fail bc x might be false
  (if (false? x) ; occurrence typing eliminates false case
      (error "failed!")
      (+ x 1))) ; x has type Int
