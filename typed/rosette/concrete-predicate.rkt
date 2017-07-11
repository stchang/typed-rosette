#lang racket/base

(provide concrete-boolean?
         concrete-integer?
         concrete-zero-integer?
         concrete-positive-integer?
         concrete-negative-integer?
         concrete-nonnegative-integer?
         concrete-real?
         concrete-positive-real?
         concrete-negative-real?
         concrete-nonnegative-real?
         )

(require (only-in racket/base
                  [boolean? concrete-boolean?]
                  [integer? concrete-integer?]
                  [real? concrete-real?]))

;; concrete-zero-integer? : Any -> Bool
(define (concrete-zero-integer? x)
  (and (concrete-integer? x) (zero? x)))

;; concrete-positive-integer? : Any -> Bool
(define (concrete-positive-integer? x)
  (and (concrete-integer? x) (positive? x)))

;; concrete-negative-integer? : Any -> Bool
(define (concrete-negative-integer? x)
  (and (concrete-integer? x) (negative? x)))

;; concrete-nonnegative-integer? : Any -> Bool
(define (concrete-nonnegative-integer? x)
  (and (concrete-integer? x) (not (negative? x))))

;; concrete-positive-real? : Any -> Bool
(define (concrete-positive-real? x)
  (and (concrete-real? x) (positive? x)))

;; concrete-negative-real? : Any -> Bool
(define (concrete-negative-real? x)
  (and (concrete-real? x) (negative? x)))

;; concrete-nonnegative-real? : Any -> Bool
(define (concrete-nonnegative-real? x)
  (and (concrete-real? x) (not (negative? x))))

