#lang rosette
 
(define-symbolic x integer?) ; defines symbolic value x
 
;; ok because Rosette lifts `integer?` to handle symbolic vals
(if (integer? x)
    (add1 x)
    (error "can't add non-int")) ; => symbolic value (+ x 1)
 
;; import raw Racket's `integer?`, as `unlifted-int?`
(require (only-in racket [integer? unlifted-int?]))
 
(if (unlifted-int? x)
    (add1 x)
    (error "can't add non-int")) ; => error
