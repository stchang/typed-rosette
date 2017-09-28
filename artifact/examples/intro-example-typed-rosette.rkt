#lang typed/rosette
(require/type racket [integer? unlifted-int? : (C→ CAny CBool)])

(define-symbolic x integer?)

;; ok because `integer?` is lifted to handle symbolic vals
(if (integer? x)
    (add1 x)
    (error "can't add non-int"))

;; type errors
(if (unlifted-int? x)
    (add1 x)
    (error "can't add non-int"))