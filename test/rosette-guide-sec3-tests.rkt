#lang typed/rosette
(require typed/lib/roseunit)

;; Examples from the Rosette Guide, Section 3

;; Symbolic effects
(: y1 #:mutable : Nat)
(define y1 0)
(check-type (if #t (void) (set! y1 3)) : CUnit -> (void))
;; y1 unchanged: 0
(check-type y1 : Nat -> 0)
(check-type (if #f (set! y1 3) (void)) : CUnit -> (void))
;; y1 unchanged: 0
(check-type y1 : Nat -> 0)
;; symbolic effect!
(define-symbolic x1 boolean?)
(typecheck-fail (define-symbolic x1 boolean? : Bool))
(check-type (if x1 (void) (set! y1 3)) : Unit -> (void))
;; y1 symbolic: (ite x1 0 3)
(check-type y1 : Nat -> (if x1 0 3))


(define res
 (let ([y #:mutable (ann 0 : Nat)])
   (if #t (void) (set! y 3))
   (printf "y unchanged: ~a\n" y)
   (if #f (set! y 3) (void))
   (printf "y unchanged: ~a\n" y)
   (let-symbolic (x boolean?)
     (if x (void) (set! y 3))
     (printf "y symbolic: ~a\n" y)
     (list x y))))

(check-type res : (CList Bool Nat))

(check-type (second res) : Nat -> (if (first res) 0 3))
;; use car and cdr instead
(check-type (car (cdr res)) : Nat -> (if (car res) 0 3))
 
;; 3.2 Solver-Aided Forms

;; 3.2.1 Symbolic Constants

(define (always-same) -> Int
  (let-symbolic (x integer?)
    x))
(check-type (always-same) : Int)
(check-type (eq? (always-same) (always-same)) : Bool -> #t)

(define (always-different) -> Int
  (let-symbolic* (x integer?)
    x))
(check-type (always-different) : Int)
(define diff-sym*1 (always-different))
(define diff-sym*2 (always-different))
(check-type (eq? diff-sym*1 diff-sym*2) : Bool -> (= diff-sym*1 diff-sym*2))

;; 3.2.2 Assertions

(check-type+asserts (assert #t) : Unit -> (void) (list))
(check-type+asserts (assert 1) : Unit -> (void) (list))
(define-symbolic x123 boolean?)
(check-type+asserts (assert x123) : Unit -> (void) (list x123))
(check-runtime-exn (assert #f "bad value"))

(check-type (asserts) : (CListof Bool) -> (list #f))
(check-type (clear-asserts!) : Unit -> (void))
(check-type (asserts) : (CListof Bool) -> (list))

;; 3.2.3 Angelic Execution
(define-symbolic x y boolean?)
(check-type (assert x) : Unit -> (void)) 
(check-type (asserts) : (CListof Bool) -> (list x))
(define solve-sol (solve (assert y)))
(check-type solve-sol : CSolution)
(check-type (sat? solve-sol) : Bool -> #t)
(check-type (evaluate x solve-sol) : Bool -> #t) ; x must be true
(check-type (evaluate y solve-sol) : Bool -> #t) ; y must be true
(check-type (solve (assert (not x))) : CSolution -> (unsat))
(clear-asserts!)

;; 3.2.4 Verification
(check-type (assert x) : Unit -> (void)) 
(check-type (asserts) : (CListof Bool) -> (list x))
(define verif-sol (verify (assert y)))
(check-type (asserts) : (CListof Bool) -> (list x))
(check-type (evaluate x verif-sol) : Bool -> #t) ; x must be true
(check-type (evaluate y verif-sol) : Bool -> #f) ; y must be false
(check-type (verify #:assume (assert y) #:guarantee (assert (and x y))) 
            : CSolution -> (unsat))
(clear-asserts!)

;; 3.2.5 Synthesis
(define-symbolic synth-x synth-c integer?)
(check-type (assert (even? synth-x)) : Unit -> (void))
(check-type (asserts) : (CListof Bool) -> (list (= 0 (remainder synth-x 2))))
(define synth-sol
  (synthesize #:forall (list synth-x)
              #:guarantee (assert (odd? (+ synth-x synth-c)))))
(check-type (asserts) : (CListof Bool) -> (list (= 0 (remainder synth-x 2))))
(check-type (evaluate synth-x synth-sol) : Int -> synth-x) ; x is unbound
(check-type (evaluate synth-c synth-sol) : Int -> 1) ; c must an odd integer
(clear-asserts!)

;; 3.2.6 Optimization
(current-bitwidth #f) ; use infinite-precision arithmetic
(define-symbolic opt-x opt-y integer?)
(check-type (assert (< opt-x 2)) : Unit -> (void))
(check-type (asserts) : (CListof Bool) -> (list (< opt-x 2)))
(define opt-sol
  (optimize #:maximize (list (+ opt-x opt-y))
            #:guarantee (assert (< (- opt-y opt-x) 1))))
; assertion store same as before
(check-type (asserts) : (CListof Bool) -> (list (< opt-x 2))) 
; x + y is maximal at x = 1 and y = 1
(check-type (evaluate opt-x opt-sol) : Int -> 1) 
(check-type (evaluate opt-y opt-sol) : Int -> 1)

;; 3.2.8 Reasoning Precision
;; see rosette-guide-sec2-tests.rkt, Sec 2.4 Symbolic Reasoning

;; ------------------------------------------------------------------------

;; Safe vector mutation

(define y2 (vector 0 1 2))

(define-symbolic b1 b2 boolean?)

;; If b1 is true, then y2[1] should be 3, otherwise y2[2] should be 4:
(check-type (if b1
                (vector-set! y2 1 3)
                (vector-set! y2 2 4))
            : Unit
            -> (void))

;; These are safe `vector-set!`s, so the state of y correctly
;; accounts for both possibilities:
;;  * If the solver finds that b1 must be #t, then the contents
;;    of y2 will be (vector 0 3 2)
;;  * Otherwise, the contents of y2 wil be (vector 0 1 4)
(check-type y2 : (MVectorof Nat)
            -> (vector 0 (if b1 3 1) (if b1 2 4)))

(define env1 (solve (assert b1)))
(check-type (evaluate y2 env1)
            : (MVectorof Nat)
            -> (vector 0 3 2))

(define env2 (solve (assert (not b1))))
(check-type (evaluate y2 env2)
            : (MVectorof Nat)
            -> (vector 0 1 4))

(define y3 (vector 0 1 2))

;; If b2 is true, then y3[1] should be 5, otherwise y3[2] should be 5:
(check-type (vector-set! y3 (if b2 1 2) 5)
            : Unit
            -> (void))

(check-type y3 : (MVectorof Nat)
            -> (vector 0 (if b2 5 1) (if b2 2 5)))

(define env3 (solve (assert b2)))
(check-type (evaluate y3 env3)
            : (MVectorof Nat)
            -> (vector 0 5 2))

(define env4 (solve (assert (not b2))))
(check-type (evaluate y3 env4)
            : (MVectorof Nat)
            -> (vector 0 1 5))

