#lang rosette/safe

;; returns true if given vector v is sorted (ascending)
(define (sorted? v)
  (define-symbolic i j integer?)
  (define max (vector-length v)) ; largest index
  ;; vector v is sorted if, for each pair of (valid) indices i j,
  ;; i < j implies v[i] <= v[j]
  (implies (and (< 0 i max) (< 0 j max) ; assume valid indices
                (< i j))
           (<= (vector-ref v i) ; check if each pair is sorted
               (vector-ref v j))))

;; returns (unique) symbolic int
(define (mk-symb-int) (define-symbolic* x integer?) x)

;; returns list of n (unique) symbolic ints
(define (mk-symb-lst n)
  (if (zero? n)
      (list)
      (cons (mk-symb-int) (mk-symb-lst (sub1 n)))))


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
(define (insert x lst)
  (if (null? lst)
      (list x)
      (let ([y (first lst)][ys (rest lst)])
        (if (< x y) (cons x lst) (cons y (insert x ys))))))

(define (insertionsort lst)
  (if (null? lst) lst (insert (first lst) (insertionsort (rest lst))))
  #;(cond [(null? lst) lst]
;        [(null? (cdr lst)) lst]
        [else (insert (car lst) (insertionsort (cdr lst)))]))

;; need assert wrapper?
(verify #:guarantee (sorted? (list->vector (insertionsort (mk-symb-lst 3)))))


;; invalid example, verify arbitrary length lists -----------------------------
;; - loops

;; (define-symbolic n integer?)
; ;(sorted? (list->vector (mergesort (mk-symb-lst n))))
