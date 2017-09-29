#lang typed/rosette
 
(define-symbolic x integer?) ; defines symbolic value x
 
;; ok because `integer?` is lifted to handle symbolic vals
(if (integer? x)
    (add1 x)
    (error "can't add non-int")) ; => symbolic value (+ 1 x)
 
;; import raw Racket's `integer?`, as `unlifted-int?`, with type
(require/type racket [integer? unlifted-int? : (C→ CAny CBool)])
 
(if (unlifted-int? x)
    (add1 x)
    (error "can't add non-int")) ; => type error
