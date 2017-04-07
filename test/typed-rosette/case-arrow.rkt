#lang typed/rosette

(require turnstile/rackunit-typechecking)

(: f1 : (Ccase-> (C→ CInt CInt)
                 (C→ Int Int)
                 (C→ CBool CBool)
                 (C→ Bool Bool)))
(define (f1 x) x)

(define-symbolic i integer?)
(define-symbolic b boolean?)

(check-type (f1 1) : CInt -> 1)
(check-type (f1 i) : Int -> i)
(check-type (f1 #true) : CBool -> #true)
(check-type (f1 b) : Bool -> b)

(: f2 : (Ccase-> (C→ CNat CNat)
                 (C→ Nat Nat)
                 (C→ CInt CInt)
                 (C→ Int Int)))
(define (f2 x) (+ x 1))

(check-type (f2 1) : CNat -> 2)
(check-type (f2 -2) : CInt -> -1)
(check-type (f2 i) : Int -> (+ i 1))
(check-type (f2 (if b 1 0)) : Nat -> (if b 2 1))

(: f3 : (Ccase-> (C→* [CNat] [[#:x CNat] [#:v CNat]] CNat)
                 (C→* [Nat] [[#:x Nat] [#:v Nat]] Nat)
                 (C→* [CInt] [[#:x CInt] [#:v CInt]] CInt)
                 (C→* [Int] [[#:x Int] [#:v Int]] Int)
                 (C→* [CNum] [[#:x CNum] [#:v CNum]] CNum)
                 (C→* [Num] [[#:x Num] [#:v Num]] Num)))
(define (f3 t #:x [x 0] #:v [v 0])
  (+ x (* v t)))

(check-type (f3 1) : CNat -> 0)
(check-type (f3 1 #:x 5) : CNat -> 5)
(check-type (f3 1 #:x 5 #:v 2) : CNat -> 7)
(check-type (f3 4 #:x 5 #:v 2) : CNat -> 13)
(check-type (f3 4 #:x 5 #:v -2) : CInt -> -3)
(check-type (f3 4 #:x i #:v -2) : Int -> (+ i -8))
(check-type (f3 4 #:v i) : Int -> (* i 4))
(check-type (f3 4 #:v (if b 2 3)) : Int -> (if b 8 12))
(check-type (f3 4.1 #:v (if b 2 3)) : Num -> (* 4.1 (if b 2 3)))

(: f4 : (Ccase-> (C→* [] [] #:rest (CListof CNat) CNat)
                 (C→* [] [] #:rest (CListof Nat) Nat)
                 (C→* [] [] #:rest (CListof CInt) CInt)
                 (C→* [] [] #:rest (CListof Int) Int)))
(define (f4 . args)
  (* 2 (apply + args)))

(check-type (f4 1 2 3) : CNat -> 12)
(check-type (f4 1 -2 3) : CInt -> 4)
(check-type (f4 1 2 i) : Int -> (* 2 (+ i 3)))
(check-type (f4 1 2 (if b 3 4)) : Nat -> (if b 12 14))

