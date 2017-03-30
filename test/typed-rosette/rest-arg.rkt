#lang typed/rosette

(require turnstile/rackunit-typechecking)

(: foldl/int : (C→ (→ Int Int Int) Int (Listof Int) Int))
(define (foldl/int f b xs)
  (if (empty? xs)
      b
      (foldl/int f (f (first xs) b) (rest xs))))

(: f : (C→* [] [] #:rest (Listof Int) Int))
(define f
  (λ xs
    (foldl/int (λ ([x : Int] [acc : Int])
                 (+ x (* 10 acc)))
               0
               xs)))

(check-type (apply f (list)) : Int -> 0)
(check-type (apply f (list 3)) : Int -> 3)
(check-type (apply f (list 4 5)) : Int -> 45)
(check-type (apply f (list 4 0 1)) : Int -> 401)
(check-type (apply f (list 2 4 6 2)) : Int -> 2462)

(check-type (f) : Int -> 0)
(check-type (f 3) : Int -> 3)
(check-type (f 4 5) : Int -> 45)
(check-type (f 4 0 1) : Int -> 401)
(check-type (f 2 4 6 2) : Int -> 2462)
