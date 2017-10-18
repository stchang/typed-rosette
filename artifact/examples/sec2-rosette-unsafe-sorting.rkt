#lang rosette

;; returns true if given vector v is sorted (ascending)
(define (sorted? v)
  (define-symbolic i j integer?)
  (define max (sub1 (vector-length v))) ; largest index
  ;; vector v is sorted if, for each pair of (valid) indices i j,
  ;; i < j implies v[i] <= v[j]
  (implies (and (<= 0 i max) (<= 0 j max) ; assume valid indices
                (< i j))
           (<= (vector-ref v i) ; check if each pair is sorted
               (vector-ref v j))))

;; returns (unique) symbolic int
(define (mk-symb-int) (define-symbolic* x integer?) x)

;; returns list of n (unique) symbolic ints
;; n must be concrete (bc for/list is unlifted)
(define (mk-symb-lst n)
  (for/list ([m n]) (mk-symb-int)))


;; merge sort --------------------------------------------------
(define (merge xs ys)
  (cond [(null? xs) ys]
        [(null? ys) xs]
        [else
         (let ([x (car xs)][y (car ys)])
           (if (< x y)
               (cons x (merge (cdr xs) ys))
               (cons y (merge xs (cdr ys)))))]))

(define (mergesort lst)
  (define n (quotient (length lst) 2))
  (if (zero? n)
      lst
      (let-values ([(fst snd) (split-at lst n)])
        (merge (mergesort fst) (mergesort snd)))))


(verify #:guarantee (assert (sorted? (list->vector (mergesort (mk-symb-lst 3))))))

;; insertion sort --------------------------------------------------
(define (splitf lst1 lst2 p?)
  (if (null? lst2)
      (list (reverse lst1) lst2)
      (if (p? (car lst2))
          (splitf (cons (car lst2) lst1) (cdr lst2) p?)
          (list (reverse lst1) lst2))))

(define (insert x lst)
  ;; good, bc reimplementing splitf uses rosette's if
  #;(match (splitf null lst #;(λ (y) (> x y)) (curry > x))
    [(list l r) #;(begin (displayln l) (displayln x) (displayln r)) (append l (cons x r))])
  ;; bad, bc splitf-at does not use rosette if
  (let-values ([(l r) (splitf-at lst #;(λ (y) (> x y)) (curry > x))])
    (append l (cons x r)))
  ;; good, manually iterate over list
  #;(match lst
    [(list) (list x)]
    [(cons y ys)
     (if (< x y)
         (cons x lst)
         (cons y (insert x ys)))]))

;; old version, manual list traversal, but with match
#;(define (insert x lst)
  (if (null? lst)
      (list x)
      (match-let ([(cons y rst) lst])
;      (let ([y (car lst)][rst (cdr lst)])
        (if (< x y)
            (cons x lst)
            (cons y (insert x rst))))))

(define/match (insertionsort lst)
  [((or (list) (list _))) lst]
  [((cons x xs)) (insert x (insertionsort xs))])

;; tests
;; (insertionsort '(1 2 3))
;; (insertionsort '(1 3 2))
;; (insertionsort '(2 1 3))
;; (insertionsort '(2 3 1))
;; (insertionsort '(3 1 2))
;; (insertionsort '(3 2 1))


(verify #:guarantee (assert (sorted? (list->vector (insertionsort (mk-symb-lst 3))))))

;; some debugging info
;bad (see insert above)
#;(|| (! (&& (&& (<= 0 i) (<= i 2)) (&& (&& (<= 0 j) (<= j 2)) (< i j))))
    (&& (&& (&& (<= 0 i) (<= i 2)) (&& (&& (<= 0 j) (<= j 2)) (< i j)))
        (<= (ite* (⊢ (= 0 i) x$2)
                  (⊢ (= 1 i) x$1)
                  (⊢ (= 2 i) x$0))
            (ite* (⊢ (= 0 j) x$2)
                  (⊢ (= 1 j) x$1)
                  (⊢ (= 2 j) x$0)))))
;good
#;(|| (! (&& (&& (<= 0 i) (<= i 2)) (&& (&& (<= 0 j) (<= j 2)) (< i j))))
    (&& (&& (&& (<= 0 i) (<= i 2)) (&& (&& (<= 0 j) (<= j 2)) (< i j)))
        (<= (ite* (⊢ (= 0 i) (ite (< x$0 (ite (< x$1 x$2) x$1 x$2))
                                  x$0
                                  (ite (< x$1 x$2) x$1 x$2)))
                  (⊢ (= 1 i) (ite (< x$0 (ite (< x$1 x$2) x$1 x$2)) ...)) ...) ...)))
