#lang turnstile

(require typed/rosette/types
         (only-in typed/rosette/base-forms expand/ro)
         (prefix-in ro: rosette)
         (postfix-in - rosette))

(provide set
         mutable-set
         set-add!
         set->list)

;; ---------------------------------
;; sets (not rosette/safe)

(define-typed-syntax set
  [_:id ≫
   ---------
   [⊢ set- ⇒ (C→* [] [] #:rest (CListof Any) (CISetof Any))]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇒ τ] ...
   --------
   [⊢ (set- e- ...) ⇒ #,(if (stx-andmap concrete? #'(τ ...))
                            #'(CISetof (CU τ ...))
                            #'(CISetof (U τ ...)))]])

(define-typed-syntax mutable-set
  [_:id ≫
   ---------
   [⊢ set- ⇒ (C→* [] [] #:rest (CListof Any) (CMSetof Any))]]
  [(_ {ty}) ≫
   --------
   [⊢ (mutable-set-) ⇒ #,(syntax/loc this-syntax (CMSetof ty))]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇒ τ] ...
   --------
   [⊢ (mutable-set- e- ...) ⇒ #,(if (stx-andmap concrete? #'(τ ...))
                            #'(CMSetof (CU τ ...))
                            #'(CMSetof (U τ ...)))]])
   
(define-typed-syntax set-add!
  [(_ s v) ≫
   [⊢ s ≫ s- ⇒ (~CMSetof τ)]
   #:fail-when (current-sym-path?) (no-mut-msg "set")
   [⊢ v ≫ v- ⇐ τ]
   ----------
   [⊢ (set-add!- s- v-) ⇒ CUnit]])

(define-typed-syntax set->list
  [(_ s) ≫
   [⊢ s ≫ s- ⇒ (~or (~CISetof τ) (~CMSetof τ))]
   ----------
   [⊢ (set->list- s-) ⇒ (CListof τ)]])
