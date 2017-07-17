#lang typed/rosette
(require typed/lib/roseunit)

;; Examples from the Rosette Guide, Section 5 Structures

; immutable transparent type
(struct point ([x : Int] [y : Int]) #:transparent)
(check-type point : (C→/sym Int Int CPoint))
(check-type point : (C→/sym Int Int (Struct point Int Int)))
(check-type point-x : (C→ CPoint Int))
(check-type point-y : (C→ CPoint Int))
(check-type point? : (C→ Any Bool))

; opaque immutable type
(struct pt ([x : Int] [y : Int]))
; mutable transparent type
(struct pnt ([x : Int] [y : Int]) #:mutable #:transparent)

(check-type (point 1 2) : CPoint -> (point 1 2))
(check-type (point 1 2) : (Struct point Int Int) -> (point 1 2))

(typecheck-fail (point #f 2) #:with-msg "expected.*Int.*given.*False")
(check-type (pt 1 2) : CPt) ; opaque, incomparable
(check-type (pnt 1 2) : CPnt -> (pnt 1 2))

(check-type (eq? (point 1 2) (point 1 2)) : Bool -> #t) ; point structures are values
(check-type (eq? (pt 1 2) (pt 1 2)) : Bool -> #f) ; pt structures are references

(check-type (eq? (pnt 1 2) (pnt 1 2)) : Bool -> #f) ; pnt structures are references

(define-symbolic b boolean?)
(define p (if b (point 1 2) (point 3 4))) ; p holds a symbolic structure
(check-type p : Point)
(check-not-type p : CPoint)
(check-type (point-x p) : Int -> (if b 1 3)) ;(ite b 1 3)
(check-type (point-y p) : Int -> (if b 2 4)) ;(ite b 2 4)
(define sol (solve (assert (= (point-x p) 3))))
(check-type (evaluate p sol) : Point -> (point 3 4)) ;#(struct:point 3 4)
(check-type (= (point-x (evaluate p sol)) 3) : Bool -> #t) 

;; Generics
(define-generics viewable
  [(view [viewable : Viewable]) -> Nat])

(typecheck-fail 
 (struct square (side)
   #:methods gen:viewable
   [(define (view self) (square-side self))])
 #:with-msg "Missing type annotations for fields")
(struct square ([side : Nat])
  #:methods gen:viewable
  [(define (view self) (square-side self))])
(struct circle ([radius : Nat])
  #:transparent
  #:methods gen:viewable
  [(define (view self) (circle-radius self))])

;(define-symbolic b boolean?)
(define p2 (if b (square 2) (circle 3))) ; p holds a symbolic structure
(check-type p2 : (U CSquare CCircle))
(check-type p2 : (U Square Circle))
(check-type (view p2) : Nat -> (if b 2 3)) ;(ite b 2 3)
(define sol2 (solve (assert (= (view p2) 3))))
(check-type (evaluate p2 sol2) : (U Square Circle) -> (circle 3))
(check-type (= (view (evaluate p2 sol2)) 3) : Bool -> #t)
