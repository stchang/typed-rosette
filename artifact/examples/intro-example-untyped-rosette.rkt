#lang rosette
 
(define-symbolic x integer?) ; defines symbolic integer x
 
;; evaluates to symbolic value (+ x 1)
;; works because Rosette's `integer?` returns true for symbolic ints
(if (integer? x)
    (add1 x)
    (error "can't add non-int"))
 
;; import raw Racket's `integer?`, as `unlifted-int?`
(require (only-in racket [integer? unlifted-int?]))
 
;; errors bc `unlifted-int?` does not recognize symbolic vals and returns false
(if (unlifted-int? x)
    (add1 x)
    (error "can't add non-int"))
