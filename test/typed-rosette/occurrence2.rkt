#lang typed/rosette

(: f : (C→ (CU CInt CFalse) CInt))
(define (f x)
  (if (not (false? x))
      (ann x : CInt)
      0))
