#lang turnstile

(provide make-hash hash-ref hash-set! hash-ref! hash-remove! hash-copy)

(require (except-in typed/rosette/base-forms #%app)
         typed/rosette/types
         (prefix-in ro: rosette))

;; ------------------------------------------------------------------------

;; Hash Tables

(define-typed-syntax make-hash
  [(_) ⇐ (~CHashof K V) ≫ --- [⊢ (ro:make-hash)]]
  [(_) ≫ --- [⊢ (ro:make-hash) ⇒ (CHashof Any Any)]]
  [(_ e:expr ~!) ≫
   [⊢ e ≫ e- ⇒ (~CListof (~CPair τ_key τ_val))]
   --------
   [⊢ (ro:make-hash e-) ⇒ (CHashof τ_key τ_val)]])

(define-typed-syntax hash-ref
  [(_ hsh:expr key:expr) ≫
   [⊢ hsh ≫ hsh- ⇒ : (~CHashof τ_key τ_val)]
   [⊢ key ≫ key- ⇐ : τ_key]
   --------
   [⊢ (ro:hash-ref hsh- key-) ⇒ : τ_val]]
  [(_ hsh:expr key:expr fail:expr) ≫
   [⊢ hsh ≫ hsh- ⇒ : (~CHashof τ_key τ_val)]
   [⊢ key ≫ key- ⇐ : τ_key]
   [⊢ fail ≫ fail- ⇐ : (C→ τ_val)]
   --------
   [⊢ (ro:hash-ref hsh- key- fail-) ⇒ : τ_val]])

(define-typed-syntax hash-set!
  [(_ hsh:expr key:expr val:expr) ≫
   [⊢ hsh ≫ hsh- ⇒ : (~CHashof τ_key τ_val)]
   [⊢ key ≫ key- ⇐ : τ_key]
   [⊢ val ≫ val- ⇐ : τ_val]
   --------
   [⊢ (ro:hash-set! hsh- key- val-) ⇒ : CVoid]])

(define-typed-syntax hash-ref!
  [(_ hsh:expr key:expr to-set:expr) ≫
   [⊢ hsh ≫ hsh- ⇒ : (~CHashof τ_key τ_val)]
   [⊢ key ≫ key- ⇐ : τ_key]
   [⊢ to-set ≫ to-set- ⇐ : (C→ τ_val)]
   --------
   [⊢ (ro:hash-ref! hsh- key- to-set-) ⇒ : τ_val]])

(define-typed-syntax hash-remove!
  [(_ hsh:expr key:expr) ≫
   [⊢ hsh ≫ hsh- ⇒ : (~CHashof τ_key τ_val)]
   [⊢ key ≫ key- ⇐ : τ_key]
   --------
   [⊢ (ro:hash-remove! hsh- key-) ⇒ : CVoid]])

(define-typed-syntax hash-copy
  [(_ hsh:expr) ≫
   [⊢ hsh ≫ hsh- ⇒ : (~CHashof τ_key τ_val)]
   --------
   [⊢ (ro:hash-copy hsh-) ⇒ : (CHashof τ_key τ_val)]])

;; ------------------------------------------------------------------------

