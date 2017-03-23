#lang racket/base
(require turnstile/examples/tests/rackunit-typechecking)
(provide (all-from-out turnstile/examples/tests/rackunit-typechecking))

(provide check-type+asserts check-type+output)
(provide check-equal?/asserts)

(require rackunit
         racket/set
         racket/string
         syntax/srcloc
         syntax/location
         (only-in rosette with-asserts)
         (for-syntax racket/base
                     syntax/parse
                     ))

(require turnstile/turnstile
;         (for-syntax turnstile/examples/tests/rackunit-typechecking)
         rackunit
         racket/port
 ;        "check-asserts.rkt"
         (only-in "../rosette.rkt" CListof Bool CUnit))

(define-binary-check (check-set=? actual expected)
  (set=? actual expected))

(define-syntax check-equal?/asserts
  (lambda (stx)
    (syntax-parse stx
      [(check-equal?/asserts actual-expr expected-expr expected-asserts-expr)
       #`(with-check-info*
          (list (make-check-name 'check-equal?/asserts)
                (make-check-location (build-source-location-list
                                      (quote-srcloc #,stx)))
                (make-check-expression '#,stx))
          (λ ()
            (test-begin
             (let-values ([(actual asserts) (with-asserts actual-expr)])
               (check-equal? actual expected-expr)
               (check-set=? asserts expected-asserts-expr)))))])))

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
