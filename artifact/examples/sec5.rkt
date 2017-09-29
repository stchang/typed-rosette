#lang typed/rosette
(require typed/lib/roseunit)

(define-symbolic x integer?)

(: add : (Ccase-> (C→ CInt CInt CInt)
                  (C→ Int CInt Int)))
(define (add x y) (+ x y))

(check-type (add 1 2) : CInt)
(check-type (add x 2) : Int)
(check-not-type (add x 2) : CInt)
(typecheck-fail (add x x)) ;; second arg must be concrete

;; add with optional arg
(: add/opt : (Ccase-> (C→* [CInt] [[#:y CInt]] CInt)
                      (C→* [Int] [[#:y CInt]] Int)))
(define (add/opt x #:y [y 0])
  (+ x y))

(check-type (add/opt 1) : CInt)
(check-type (add/opt x) : Int)
(check-not-type (add/opt x) : CInt)
(check-type (add/opt 1 #:y 2) : CInt)
(check-type (add/opt x #:y 2) : Int)
(check-not-type (add/opt x #:y 2) : CInt)
(typecheck-fail (add/opt x #:y x)) ;; second arg must be concrete

; paper sec 5.4: type system imprecision

(define-symbolic b boolean?)

;; EXAMPLE 1:

;; this expression evaluates to a concrete 2,
;; but gets assigned symbolic type due to the symbolic b
(if b 2 2)

;; thus Typed Rosette rejects this function call
(typecheck-fail (add 1 (if b 2 2))) ; second arg must be concrete

;; we can use occurrence types to help:
;; term? returns true if its argument is symbolic,
;; thus we can refine to be concrete in the "else" branch
(let ([x (if b 2 2)])
  (if (term? x)
      (error "expected concrete val")
      (add 1 x))) ; => 3


;; EXAMPLE 2:

;; this expression evaluates to concrete 3 in untyped Rosette,
;; because Rosette prunes infeasible paths,
;; but Typed Rosette rejects the program due to the (if b 2 "bad"),
;; which it determines to have type (U Int String),
;; which is incompatible with plus
(typecheck-fail (+ 1 (if b 2 "bad")))

;; here we need an annotation to help the type checker
;; assert-type refines the type as directed but inserts dynamic checks
;; to preserve safety
(+ 1 (assert-type (if b 2 "bad") : Int)) ; => 3
