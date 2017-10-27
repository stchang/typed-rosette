#lang typed/rosette

;; returns true if given vector v is sorted (ascending)
(define (sorted? [v : (CMVectorof Int)]) -> Bool
  (let-symbolic [i j integer?]
    (let ([max (sub1 (vector-length v))]) ; largest index
      ;; vector v is sorted if, for each pair of (valid) indices i j,
      ;; i < j implies v[i] <= v[j]
      (implies (and (<= 0 i max) (<= 0 j max) ; assume valid indices
                    (< i j))
               (<= (vector-ref v i) ; check if each pair is sorted
                   (vector-ref v j))))))

;; returns (unique) symbolic int
(define (mk-symb-int) -> Int
  (let-symbolic* [x integer?] x))

;; returns list of n (unique) symbolic ints
;; n has concrete type (bc for/list is unlifted)
(define (mk-symb-lst [n : CNat]) -> (CListof Int)
  (for/list ([m (in-range n)]) (mk-symb-int)))


;; merge sort --------------------------------------------------

;; manually re-implementing this instead of using split-at
;; bc typed rosette doesnt support multi-return values yet
(define (split [lst1 : (CListof Int)] [lst2 : (CListof Int)] [n : CInt]) -> (CList (CListof Int) (CListof Int))
  (if (zero? n)
      (list lst1 (reverse lst2))
      (split (cdr lst1) (cons (car lst1) lst2) (sub1 n))))

(define (merge [xs : (CListof Int)] [ys : (CListof Int)]) -> (CListof Int)
  (unsafe-cast-concrete
   (if (null? xs) ys
       (if (null? ys) xs
           (let ([x (car xs)][y (car ys)])
             (if (< x y)
                 (cons x (merge (cdr xs) ys))
                 (cons y (merge xs (cdr ys))))))))
  #;(cond [(null? xs) ys]
        [(null? ys) xs]
        [else
         (let ([x (car xs)][y (car ys)])
           (if (< x y)
               (cons x (merge (cdr xs) ys))
               (cons y (merge xs (cdr ys)))))]))


(define (mergesort [lst : (CListof Int)]) -> (CListof Int)
  (let ([n (quotient (length lst) 2)])
    (if (zero? n)
        lst
        (let ([lsts (split lst (list) n)])
          (let ([fst (first lsts)]
                [snd (second lsts)])
            (merge (mergesort fst) (mergesort snd)))))))

;; (mergesort '(1 2 3))
;; (mergesort '(1 3 2))
;; (mergesort '(2 1 3))
;; (mergesort '(2 3 1))
;; (mergesort '(3 1 2))
;; (mergesort '(3 2 1))

(verify #:assume #t
        #:guarantee (assert (sorted? (list->vector (mergesort (mk-symb-lst 3))))))


;; insertion sort --------------------------------------------------
(define (splitf [lst1 : (CListof Int)]
                [lst2 : (CListof Int)]
                [p? : (C→ Int Any)]) -> (CList (CListof Int) (CListof Int))
  (let ([res
         (if (null? lst2)
             (list (reverse lst1) lst2)
             (if (p? (car lst2))
                 (splitf (cons (car lst2) lst1) (cdr lst2) p?)
                 (list (reverse lst1) lst2)))])
    (list (unsafe-cast-concrete (car res))
          (unsafe-cast-concrete (car (cdr res))))))

(require/type
 racket/list
 [splitf-at r:splitf-at : (C→ (CListof Int)
                              (C→ Int CBool)
                              (CList (CListof Int) (CListof Int)))])

(define (insert [x : Int] [lst : (CListof Int)]) -> (CListof Int)
  ;; good, with manually implemented splitf
  #;(let ([l+r (splitf (list) lst (λ ([y : Int]) (> x y)) #;(curry > x))])
    (append (car l+r) (cons x (car (cdr l+r)))))
  ;; bad, splitf-pred must return conc val, bc it gets unsed in unlifted if
  #;(let ([l+r (r:splitf-at lst (λ ([y : Int]) (> x y)) #;(curry > x))]) ; racket version
    (append (car l+r) (cons x (car (cdr l+r)))))
#;  (let ([l+r (splitf-at lst (λ ([y : Int]) (> x y)) #;(curry > x))])
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

(verify #:assume #t
        #:guarantee (assert (sorted? (list->vector (insertionsort (mk-symb-lst 3))))))

;; bad example --------------------------------------------------
;(define-symbolic n integer?)

;(sorted? (list->vector (mergesort (mk-symb-lst n))))
