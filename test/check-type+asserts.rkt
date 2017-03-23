#lang racket/base

(provide check-type+asserts check-type+synth-output)

(require turnstile/turnstile
         turnstile/examples/tests/rackunit-typechecking
         rackunit
         racket/string
         racket/port
         "check-asserts.rkt"
         (only-in "../typed/rosette.rkt" CListof Bool CUnit))

(define-typed-syntax check-type+asserts #:datum-literals (: ->)
  [(_ e : τ-expected -> v asserts) ≫
   [⊢ [e ≫ e- ⇐ : τ-expected]]
   --------
   [⊢ [_ ≫ (check-equal?/asserts e-
                                 (add-expected v τ-expected)
                                 (add-expected asserts (CListof Bool)))
         ⇒ : CUnit]]])

(define-syntax (check-type+synth-output stx)
  (syntax-parse stx
    [(_ e str)
     #'(begin
         (check-type e : CUnit)
         (check-true
          (string-contains? (with-output-to-string (λ () e)) str)))]))
