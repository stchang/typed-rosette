#lang typed/rosette

(require turnstile/rackunit-typechecking)

(: foldl/int : (C→ (→ Int Int Int) Int (CListof Int) Int))
(define (foldl/int f b xs)
  (if (empty? xs)
      b
      (foldl/int f (f (first xs) b) (rest xs))))

(: f : (C→* [] [] #:rest (CListof Int) Int))
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

(check-type (+ 1 2 3 4 5 6 7 8 9 10) : CNat -> 55)
(check-type (+ 1 -2 3 -4 5 -6 7 -8 9 -10) : CInt -> -5)

