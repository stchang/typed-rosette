#lang rosette/safe

(define-symbolic i integer?)
(+ i 1) ; => i+1

(define-symbolic b boolean?)
(if b 1 (+ i 2)) ; => <[b: 1][¬b: i + 2]> (symbolic union value)

(solve (assert (= i 3))) ; => model: i = 3

;; returns true if given vector v is sorted (ascending)
(define (sorted? v)
  (define-symbolic i j integer?)
  (define max (sub1 (vector-length v))) ; largest index
  (implies (and (<= 0 i max) (<= 0 j max) ; assume valid indices
                (< i j))
           (<= (vector-ref v i) ; check if each pair is sorted
               (vector-ref v j))))

;; attempt to verify sortedness of vector of concrete ints
;; - finds counterexample
(verify (assert (sorted? (vector 3 5 4)))) ; => ✗: i = 1, j = 2

;; attempt to verify sortedness of vector of symbolic ints,
;; given constraints x < y < z
(define-symbolic x y z integer?)
(define vec (vector x y z))
;; unsat == cannot find counterexample == all assertions satisfied
(verify #:assume (assert (and (< x y) (< y z)))
        #:guarantee (assert (sorted? vec))) ; ✓
