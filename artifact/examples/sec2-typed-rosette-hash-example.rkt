#lang typed/rosette

;; returns true if given hash h, with concrete int indices, is sorted, ascending
(define (sorted-hash? [h : (CHashTable CInt Int)]) -> Bool
  (let-symbolic [i j integer?]
    (let ([max (sub1 (hash-count h))]) ; largest index
      (implies (and (<= 0 i max) (<= 0 j max) ; assume valid indices
                    (< i j))
               ;; hash-ref does not recognize symbolic values
               ;; - results in type error
               (<= (hash-ref h i) ; check if each pair is sorted
                   (hash-ref h j))))))

;; attempt to verify sortedness of hash mapping concrete ints to symbolic ints,
;; given constraints x < y < z
(define-symbolic x y z integer?)

(define h : (CHashTable CInt Int)
  (hash 0 x 1 y 2 z))

(verify #:assume (assert (and (< x y) (< y z)))
        #:guarantee (assert (sorted-hash? h))) ; => type error
