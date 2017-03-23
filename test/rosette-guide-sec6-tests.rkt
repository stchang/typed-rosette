#lang s-exp "../typed/rosette.rkt"
(require typed/lib/roseunit)

;; Examples from the Rosette Guide, Section 6 Libraries

;; 6.2.1 Synthesis library
(require "../typed/lib/synthax.rkt")

;; choose
(define (div2 [x : BV] -> BV)
  ([choose bvshl bvashr bvlshr bvadd bvsub bvmul] x (?? (bitvector 8))))
(define-symbolic i (bitvector 8))
(check-type+output
 (print-forms
  (synthesize #:forall (list i)
              #:guarantee (assert (equal? (div2 i) (bvudiv i (bv 2 8))))))
 -> "(define (div2 (x : BV) -> BV) (bvlshr x (bv 1 8)))")

;; define-synthax
(define-synthax (nnf [x : Bool] [y : Bool] depth -> Bool)
 #:base (choose x (! x) y (! y))
 #:else (choose
         x (! x) y (! y)
         ((choose && ||) (nnf x y (- depth 1))
                         (nnf x y (- depth 1)))))
(define (nnf=> [x : Bool] [y : Bool] -> Bool)
  (nnf x y 1))

(define-symbolic a b boolean?)
(check-type+output
 (print-forms
  (synthesize
   #:forall (list a b)
   #:guarantee (assert (equal? (=> a b) (nnf=> a b)))))
 -> "(define (nnf=> (x : Bool) (y : Bool) -> Bool) (|| (! x) y))")

;; 6.2.2 Angelic Execution Library
(require "../typed/lib/angelic.rkt")

(define (static -> Int)  (choose 1 2 3))
(define (dynamic -> Int) (choose* 1 2 3))
(check-type (equal? (static) (static)) : Bool -> #t)
(define dyn1 (dynamic))
(define dyn2 (dynamic))
(check-type (equal? dyn1 dyn2) : Bool -> (equal? dyn1 dyn2))
;(= (ite xi?$4 1 (ite xi?$5 2 3)) (ite xi?$6 1 (ite xi?$7 2 3)))

