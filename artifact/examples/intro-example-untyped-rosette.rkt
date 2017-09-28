#lang rosette
(require (only-in racket [integer? unlifted-int?]))

(define-symbolic x integer?)

;; ok because `integer?` is lifted to handle symbolic vals
(if (integer? x)
    (add1 x)
    (error "can't add non-int"))

;; errors
(if (unlifted-int? x)
    (add1 x)
    (error "can't add non-int"))