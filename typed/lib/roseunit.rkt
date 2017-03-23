#lang racket/base
(require turnstile/rackunit-typechecking "check-asserts.rkt"
         turnstile/turnstile
         (only-in "../rosette.rkt" CListof Bool CUnit)
         racket/string racket/port
         syntax/srcloc syntax/location
         (for-syntax racket/base syntax/parse))

(provide (all-from-out turnstile/rackunit-typechecking "check-asserts.rkt"))
(provide check-type+asserts check-type+output)

(define-typed-syntax check-type+asserts #:datum-literals (: ->)
  [(_ e : τ-expected -> v asserts) ≫
   [⊢ [e ≫ e- ⇐ : τ-expected]]
   --------
   [⊢ [_ ≫ (check-equal?/asserts e-
                                 (add-expected v τ-expected)
                                 (add-expected asserts (CListof Bool)))
         ⇒ : CUnit]]])

(define-syntax (check-type+output stx)
  (syntax-parse stx
    [(_ e (~datum ->) str ...)
     #`(with-check-info*
         (list (make-check-name 'check-type+output)
               (make-check-location (build-source-location-list
                                     (quote-srcloc #,stx)))
               (make-check-expression '#,stx))
         (λ ()
           (test-begin
             (check-type e : CUnit)
             (let ([out (with-output-to-string (λ () e))])
               (check-true (string-contains? out str)) ...))))]))
