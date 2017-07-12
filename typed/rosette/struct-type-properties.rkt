#lang turnstile

(provide prop:procedure
         struct-field-index)

(require (prefix-in ro: rosette/safe)
         "types.rkt"
         "base-forms.rkt"
         "unsafe.rkt")

;; TODO:
;; Add a way to specify how properties like prop:procedure
;; can add to the types of structs that implement it.

(: prop:procedure : (CStructTypeProp CNat))
(define prop:procedure
  (unsafe-assign-type ro:prop:procedure : (CStructTypeProp CNat)))

(define-typed-syntax struct-field-index
  [(_ field:id) ≫
   --------
   [⊢ (ro:struct-field-index field) ⇒ CNat]])

