#lang typed/rosette
(require typed/lib/roseunit)

(define-symbolic b boolean?)
(define-symbolic i integer?)
(define x 9)
(define x-sym (add1 i))

(typecheck-fail (if b (set! x 10) (set! x 11))
 #:with-msg "Cannot mutate concrete variable x when in a symbolic path")

(if b 
    (set! x-sym 10)
    (set! x-sym 11))

(check-type x-sym : Int -> (if b 10 11))

(define y (vector 0 1 2))
(check-type y : (CMVectorof CNat))

; If b is true, then y[1] should be 3, otherwise y[2] should be 4:
(typecheck-fail (if b (vector-set! y 1 3) (vector-set! y 2 4))
 #:with-msg "Cannot mutate concrete vector elements when in a symbolic path")

(define vec-sym (vector (ann 0 : Nat) 1 2))
(check-type vec-sym : (CMVectorof Nat))
(check-not-type vec-sym : (CMVectorof CNat))

(if b (vector-set! vec-sym 1 3) (vector-set! vec-sym 2 4))

; The state of vec-sym correctly accounts for both possibilities:
;  * If the solver finds that b must be #t, then the contents
;    of y will be #(0 3 2).
;  * Otherwise, the contents of y will be #(0 1 4)
(check-type vec-sym : (CMVectorof Nat) -> (vector 0 (if b 3 1) (if b 2 4)))

(define env1 (solve (assert b)))
(check-type (evaluate vec-sym env1) : (CMVectorof Nat) -> (vector 0 3 2))
;'#(0 3 2)
(define env2 (solve (assert (not b))))
(check-type (evaluate vec-sym env2) : (CMVectorof Nat) -> (vector 0 1 4))
;'#(0 1 4)

;; unsafe
(define h (make-hash (ann '((1 . 2)) : (CListof (CPair CNat CNat)))))
(check-type h : (CHashTable CNat CNat))
(define-symbolic key integer?)
 
; The following call produces an incorrect value. Intuitively, we expect the
; output to be the symbolic number that is either 2 or 0, depending on whether
; the key is 1 or something else.
; ... but Typed Rosette catches it
(typecheck-fail (hash-ref h key 0)
 #:with-msg "hash-ref: type mismatch: expected CNat, given.*\\(Term CInt\\)")
;(check-type (hash-ref h key 0) : CInt -> 0) ; untyped rosette does this

; The following call produces an incorrect state. Intuitively, we expect h
; to be empty if b is true and unchanged otherwise.
(typecheck-fail (when b (hash-clear! h))
 #:with-msg "Cannot mutate concrete hash h when in a symbolic path")

(typecheck-fail (unless b (hash-clear! h))
 #:with-msg "Cannot mutate concrete hash h when in a symbolic path")

(typecheck-fail (unless b (hash-ref! h 1 2))
 #:with-msg "Cannot mutate concrete hash h when in a symbolic path")

(typecheck-fail (when b (hash-set! h 1 2))
 #:with-msg "Cannot mutate concrete hash h when in a symbolic path")

(typecheck-fail (when b (hash-remove! h 1))
 #:with-msg "Cannot mutate concrete hash h when in a symbolic path")

(typecheck-fail (when b (set-add! (set 1 2) 3)))

(define/conc (f [x : Int]) -> Int (add1 x))

(typecheck-fail (when b (f 1))
 #:with-msg "Cannot apply function with C→/conc type when in a symbolic path")

(define (g [x : Int]) -> Int (add1 x))

(check-type (if b (g 1) (g 2)) : Int -> (if b 2 3))

;; It's not possible to call whole-data structure mutating fns
;; when in a symbolic path, unless those fns know how to handle symbolic args.
;; So this excludes data structures not in rosette/safe, eg hash tables.
;; (define hsym (ann (hash 1 2) : (U (CHashTable CPosInt CPosInt))))
;; (when b (hash-clear! hsym))


(typecheck-fail/toplvl (define (f2) -> CUnit (set! x 2))
 #:with-msg "Cannot mutate concrete variable x when in a symbolic path")

(define/conc (f2) -> CUnit (set! x 2))

;; sym path introduced in both makes this not ok, despite define/conc
(typecheck-fail/toplvl
 (define/conc (f3) -> CUnit (when b (set! x 2)))
 #:with-msg "Cannot mutate concrete variable x when in a symbolic path")

;; The following defs/exprs are safe but require "sym scopes" 
;; to satisfy the type checker

(define (f4 [x : CInt]) -> CInt (set! x 1) x)

(typecheck-fail/toplvl
 (define (f5 [x : CInt]) -> CInt (when b (set! x 1) x))
 #:with-msg "Cannot mutate concrete variable x when in a symbolic path")

(check-type
 (if b
     (let ([x 1]) (set! x 2) x)
     (let ([y 3]) (set! y 4) y))
 : PosInt -> (if b 2 4))
