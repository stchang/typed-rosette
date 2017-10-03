#lang typed/rosette
(require typed/lib/roseunit)

;; paper sec 5.3: concreteness polymorphism in practice

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
