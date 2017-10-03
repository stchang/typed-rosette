#lang rosette ; allows lenient symbolic execution

;; returns true if given hash h, with integer indices, is sorted (ascending)
(define (sorted-hash? h)
  (define-symbolic i j integer?)
  (define max (sub1 (hash-count h))) ; largest index
  ;; hash h is "sorted" if, for each pair of (valid) keys i j,
  ;; i < j implies h[i] <= h[j]
  (implies (and (<= 0 i max) (<= 0 j max) ; assume valid indices
                (< i j))
           ;; hash-ref does not recognize symbolic values,
           ;; but is given symbolic int
           (<= (hash-ref h i) ; check if each pair is sorted
               (hash-ref h j))))

;; attempt to verify sortedness of hash mapping concrete ints to symbolic ints,
;; given constraints x < y < z
(define-symbolic x y z integer?)

(define h (hash 0 x
                1 y
                2 z))

;; erroneously produces "counterexample" that is actually sorted
(verify #:assume (assert (and (< x y) (< y z)))
        #:guarantee (assert (sorted-hash? h))) ; => ✗: x=-1, y=0, z=1, i=0, j=1
