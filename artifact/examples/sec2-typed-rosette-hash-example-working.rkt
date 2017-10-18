#lang typed/rosette

;; returns true if given hash h, with concrete int indices, is sorted, ascending
;; can't use hash-ref bc it's unlifted
;; instead, manually generate constraints for each pair of indices
(define (sorted-hash? [h : (CHashTable CNat Int)]) -> Bool
    (let ([count (hash-count h)]) ; size
      ;; manually iterate over hash table
      ;; hash h is "sorted" if, for each pair of (valid) keys i j,
      ;; i < j implies h[i] <= h[j]
      (for*/fold ([result #t])
                 ([i (in-range count)]
                  [j (in-range count)])
        (and (implies (< i j)
                      (<= (hash-ref h i)
                          (hash-ref h j)))
             result))))

;; attempt to verify sortedness of hash mapping concrete ints to symbolic ints,
;; given constraints x < y < z
(define-symbolic x y z integer?)

(define h : (CHashTable CNat Int)
  (hash 0 x 1 y 2 z))

(verify #:assume (assert (and (< x y) (< y z)))
        #:guarantee (assert (sorted-hash? h))) ; => type error

;; insertion sort --------------------------------------------------

;; returns (unique) symbolic int
(define (mk-symb-int) -> Int
  (let-symbolic* [x integer?] x))

;; returns list of n (unique) symbolic ints
;; n has concrete type (bc for/list is unlifted)
(define (mk-symb-lst [n : CNat]) -> (CListof Int)
  (for/list ([m (in-range n)]) (mk-symb-int)))

;; insertion sort --------------------------------------------------
(define (insert [x : Int] [lst : (CListof Int)]) -> (CListof Int)
  ;; bad, splitf-pred must return conc val, bc it gets unsed in unlifted if
  #;(let ([l+r (splitf-at lst (λ ([y : Int]) (> x y)) #;(curry > x))])
    (append (car l+r) (cons x (car (cdr l+r)))))
  ;; good, manually use (lifted) if
  (unsafe-cast-concrete
   (if (null? lst)
       (list x)
       (let ([y (car lst)][rst (cdr lst)])
         (if (< x y)
             (cons x lst)
             (cons y (insert x rst)))))))

(define (insertionsort [lst : (CListof Int)]) -> (CListof Int)
  (cond [(null? lst) lst]
        [(null? (cdr lst)) lst]
        [else (insert (car lst) (insertionsort (cdr lst)))]))

;; (insertionsort '(1 2 3))
;; (insertionsort '(1 3 2))
;; (insertionsort '(2 1 3))
;; (insertionsort '(2 3 1))
;; (insertionsort '(3 1 2))
;; (insertionsort '(3 2 1))

(define (list->hash [lst : (CListof Int)]) -> (CHashTable CNat Int)
  (for/hash ([i (in-range (length lst))]
             [x (in-list lst)])
    #:key i #:val x))

(verify #:assume #t
        #:guarantee (assert (sorted-hash? (list->hash (insertionsort (mk-symb-lst 3))))))

