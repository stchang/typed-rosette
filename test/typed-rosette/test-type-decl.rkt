#lang typed/rosette

(require turnstile/rackunit-typechecking)

(: f : (C→ Int Int))
(define f
  (λ (x) (g x x)))

(: g : (C→ Int Int Int))
(define g
  (λ (x y) (+ x y)))

(check-type (f 3) : Int -> 6)

(define var 1)

(check-type var : PosInt -> 1)

