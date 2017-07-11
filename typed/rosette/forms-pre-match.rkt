#lang turnstile

(provide quote)

(require "types.rkt"
         (rename-in "base-forms.rkt" [#%app app])
         "bool.rkt"
         (prefix-in ro: rosette)
         (prefix-in stlc+union: turnstile/examples/stlc+union)
         )

;; ------------------------------------------------------------------------

;; quote

(define-typed-syntax quote
  ;; base case: symbol
  [(_ x:id) ≫
   --------
   [⊢ (ro:quote x) ⇒ CSymbol]]
  ;; recur: list (this clause should come before pair)
  [(_ (x ...)) ≫
   [⊢ (quote x) ≫ (_ x-) ⇒ τ] ...
   --------
   [⊢ (ro:quote (x- ...)) ⇒ (CList τ ...)]]
  ;; recur: pair
  [(_ (x . y)) ≫
   [⊢ (quote x) ≫ (_ x-) ⇒ τx]
   [⊢ (quote y) ≫ (_ y-) ⇒ τy]
   --------
   [⊢ (ro:quote (x- . y-)) ⇒ (CPair τx τy)]]
  ;; base case: other datums
  [(_ x) ≫
   [⊢ (stlc+union:#%datum . x) ≫ (_ x-) ⇒ τ]
   --------
   [⊢ (ro:quote x-) ⇒ τ]])

;; ------------------------------------------------------------------------

