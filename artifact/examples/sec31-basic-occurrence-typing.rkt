#lang typed/rosette

(define (f [x : (CU CInt CString)]) -> CInt
  (if (integer? x)
      (add1 x)
      (string-length x)))

(f 10)
(f "ten")

(define-symbolic i integer?)
(define-symbolic b boolean?)
(define (f2 [x : (U Int Bool)]) -> Int
  (if (integer? x)
      (add1 x)
      (if x 10 11)))

(f2 i)
(f2 b)

(define (g [x : (CU CInt CString)]) -> CInt
  (if (integer? (and x)) ; pred arg is expression instead of variable
      (add1 x)
      (string-length x)))

(g 10)
(g "ten")
