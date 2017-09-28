#lang rosette ; allows lenient symbolic execution

(define (sorted-hash? h)
  (define-symbolic i j integer?)
  (define max (sub1 (hash-count h))) ; largest index
  (implies (and (<= 0 i max) (<= 0 j max) ; assume valid indices
                (< i j))
           ;; hash-ref does not recognize symbolic values
           (<= (hash-ref h i) ; check if each pair is sorted
               (hash-ref h j))))

(define-symbolic x y z integer?)

(define h (hash 0 x 1 y 2 z))

;; erroneously produces "counterexample" that is actuall sorted
(verify #:assume (assert (and (< x y) (< y z)))
        #:guarantee (assert (sorted-hash? h))) ; => ✗: x=-1, y=0, z=1, i=0, j=1