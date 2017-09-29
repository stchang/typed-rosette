#lang typed/rosette

(define (f [x : (CU CInt CString)]) -> CInt
  (if (integer? x)
      (add1 x)
      (string-length x)))

(f 10)
(f "ten")

(define (g [x : (CU CInt CString)]) -> CInt
  (if (integer? (and x)) ; pred arg is expression instead of variable
      (add1 x)
      (string-length x)))

(g 10)
(g "ten")
