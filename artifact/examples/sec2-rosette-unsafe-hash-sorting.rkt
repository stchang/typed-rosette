#lang rosette

;; returns true if given vector v is sorted (ascending)
#;(define (sorted? v)
  (define-symbolic i j integer?)
  (define max (sub1 (vector-length v))) ; largest index
  ;; vector v is sorted if, for each pair of (valid) indices i j,
  ;; i < j implies v[i] <= v[j]
  (implies (and (<= 0 i max) (<= 0 j max) ; assume valid indices
                (< i j))
           (<= (vector-ref v i) ; check if each pair is sorted
               (vector-ref v j))))

;; returns true if given hash h, with concrete int indices, is sorted, ascending
(define (sorted-hash? h)
  (define-symbolic* i j integer?)
  (let ([size (sub1 (hash-count h))]) ; largest index
    ;; hash h is "sorted" if, for each pair of (valid) keys i j,
    ;; i < j implies h[i] <= h[j]
#;      (for*/fold ([result #t])
                 ([i (in-range size)]
                  [j (in-range size)])
        (and (implies (< i j)
                      (<= (hash-ref h i)
                          (hash-ref h j)))
             result))
    (implies (and (<= 0 i size) (<= 0 j size) ; assume valid indices
                  (< i j))
             ;; hash-ref does not recognize symbolic values
             ;; - results in type error
             (<= (hash-ref h i) ; check if each pair is sorted
                 (hash-ref h j)))))

(define (list->hash lst)
  (for/hash ([i (in-range (length lst))]
             [x (in-list lst)])
    (values i x)))

;; returns (unique) symbolic int
(define (mk-symb-int) (define-symbolic* x integer?) x)

;; returns list of n (unique) symbolic ints
;; n must be concrete (bc for/list is unlifted)
(define (mk-symb-lst n)
  (for/list ([m n]) (mk-symb-int)))


;; merge sort --------------------------------------------------
(define/match (merge l1 l2)
  [('() _) l2]
  [(_ '()) l1]
  [((cons x xs) (cons y ys))
   (if (< x y)
       (cons x (merge xs l2))
       (cons y (merge l1 ys)))])
#;(define (merge xs ys)
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


;(verify #:guarantee (assert (sorted? (list->vector (mergesort (mk-symb-lst 3))))))

;; insertion sort --------------------------------------------------
(define (splitf lst1 lst2 p?)
  (if (null? lst2)
      (list (reverse lst1) lst2)
      (if (p? (car lst2))
          (splitf (cons (car lst2) lst1) (cdr lst2) p?)
          (list (reverse lst1) lst2))))

#;(define/match (insert x lst)
  [(_ '()) (list x)]
  [(_ (cons y ys)) (if (< x y)
                       (cons x lst)
                       (cons y (insert x ys)))])
(define (insert x lst)
  ;; good, bc reimplementing splitf uses rosette's if
  #;(match (splitf null lst #;(λ (y) (> x y)) (curry > x))
      [(list l r) #;(begin (displayln l) (displayln x) (displayln r)) (append l (cons x r))])
  ;; bad, bc splitf-at does not use rosette if
#;  (let-values ([(l r) (splitf-at lst #;(λ (y) (> x y)) (curry > x))])
    (append l (cons x r)))
  ;; good, manually iterate over list
  (match lst
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
(require (for-syntax syntax/parse racket/syntax))
(define-syntax (def/match stx)
  (syntax-parse stx
    [(_ f [p e] ...)
     #:with x (generate-temporary)
     #'(define (f x) (match x [p e] ...))]))
(define/match (insertionsort lst)
;  [((list)) (list)]
  [('()) lst]
  [((cons x xs)) (insert x (insertionsort xs))])
#;(def/match insertionsort
  [(list) (list)]
  [(cons x xs) (insert x (insertionsort xs))])

;; tests
;; (insertionsort '(1 2 3))
;; (insertionsort '(1 3 2))
;; (insertionsort '(2 1 3))
;; (insertionsort '(2 3 1))
;; (insertionsort '(3 1 2))
;; (insertionsort '(3 2 1))

;; need assert wrapper?
;(verify #:guarantee (assert (sorted? (list->vector (insertionsort (mk-symb-lst 3))))))
;(verify (assert (sorted? (list->vector (insertionsort (mk-symb-lst 3))))))

;; ;; attempt to verify sortedness of hash mapping concrete ints to symbolic ints,
;; ;; given constraints x < y < z
(define-symbolic* x y z integer?)

;; (define h : (CHashTable CInt Int)
;;   (hash 0 x 1 y 2 z))

;; (verify #:assume (assert (and (< x y) (< y z)))
;;         #:guarantee (assert (sorted-hash? h))) ; => type error

(verify (assert (sorted-hash? (list->hash (insertionsort (list x y z)#;(mk-symb-lst 3))))))
