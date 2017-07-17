#lang turnstile

(provide hash make-hash
         hash-ref hash-set hash-keys hash-has-key?
         hash-set! hash-ref! hash-remove! hash-clear! hash-copy)

(require (except-in typed/rosette/base-forms #%app)
         typed/rosette/types
         (prefix-in ro: rosette))

;; ------------------------------------------------------------------------

;; Hash Tables

;; TODO: distinguish mutable and immutable hash tables

(define-typed-syntax make-hash
  [(_) ⇐ (~CHashof K V) ≫ --- [⊢ (ro:make-hash)]]
  [(_) ≫ --- [⊢ (ro:make-hash) ⇒ (CHashof Any Any)]]
  [(_ e:expr ~!) ≫
   [⊢ e ≫ e- ⇒ (~CListof (~CPair τ_key τ_val))]
   --------
   [⊢ (ro:make-hash e-) ⇒ (CHashof τ_key τ_val)]])

(define-typed-syntax hash
  ;; empty
  [(_) ≫
   ----------
   [#:error "add annotations"]]
  [(_ {tyk tyv}) ≫
   ----------
   [⊢ (hash-) ⇒ (CHashTable tyk tyv)]]
  [(_ (~seq k v) ...) ≫
   [⊢ k ≫ k- ⇒ tyk] ...
   [⊢ v ≫ v- ⇒ tyv] ...
   #:when (and (same-types? #'(tyk ...))
               (same-types? #'(tyv ...)))
   #:with tyk1 (stx-car #'(tyk ...))
   #:with tyv1 (stx-car #'(tyv ...))
   #:with (k+v ...) (stx-flatten #'((k- v-) ...))
   ----------
   [⊢ (hash- k+v ...) ⇒ (CHashTable tyk1 tyv1)]])

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

(define-typed-syntax hash-set
  [(_ e k v) ≫
   [⊢ e ≫ e- ⇒ (~and ty-out (~CHashTable τk τv))]
   [⊢ k ≫ k- ⇐ τk]
   [⊢ v ≫ v- ⇐ τv]
   --------
   [⊢ (hash-set- e- k- v-) ⇒ ty-out]])

(define-typed-syntax hash-keys
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~CHashTable τ _)]
   --------
   [⊢ (hash-keys- e-) ⇒ (CListof τ)]])

(define-typed-syntax hash-has-key?
  [(_ e k) ≫
   [⊢ e ≫ e- ⇒ (~CHashTable τk _)]
   [⊢ k ≫ k- ⇐ τk]
   --------
   [⊢ (hash-has-key?- e- k-) ⇒ CBool]])

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

(define-typed-syntax hash-clear!
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~CHashTable _ _)]
   --------
   [⊢ (hash-clear!- e-) ⇒ CUnit]])

(define-typed-syntax hash-copy
  [(_ hsh:expr) ≫
   [⊢ hsh ≫ hsh- ⇒ : (~CHashof τ_key τ_val)]
   --------
   [⊢ (ro:hash-copy hsh-) ⇒ : (CHashof τ_key τ_val)]])

;; ------------------------------------------------------------------------

