#lang turnstile

(require typed/rosette/types
         (prefix-in ro: rosette)
         (postfix-in - rosette))

;; ------------------------------------------------------------------------

(provide (typed-out [vector? : LiftedPred]))

(provide vector vector-immutable make-vector vector-ref vector-set!)

;; mutable constructor
(define-typed-syntax vector
  [(_ e:expr ...) ≫
   [⊢ [e ≫ e- ⇒ : τ] ...]
   #:with τ* (type-merge*
              (stx-map type-merge #'[τ ...] #'[τ ...]))
   --------
   [⊢ [_ ≫ (ro:vector e- ...) ⇒ : (CMVectorof (U τ*))]]])

;; immutable constructor
(define-typed-syntax vector-immutable
  [(_ e:expr ...) ≫
   [⊢ [e ≫ e- ⇒ : τ] ...]
   --------
   [⊢ [_ ≫ (ro:vector-immutable e- ...) ⇒ : #,(if (stx-andmap concrete? #'(τ ...))
                                                  #'(CIVectorof (CU τ ...))
                                                  #'(CIVectorof (U τ ...)))]]])

(define-typed-syntax make-vector
  [(_ size:expr v:expr) ≫
   [⊢ size ≫ size- ⇐ CNat]
   [⊢ v ≫ v- ⇒ τ]
   --------
   [⊢ (ro:make-vector size- v-) ⇒ (CMVectorof τ)]])

(define-typed-syntax vector-ref
  [(_ v:expr i:expr) ≫
   [⊢ [v ≫ v- ⇒ : (~or (~CMVectorof τ) (~CIVectorof τ))]]
   [⊢ [i ≫ i- ⇐ : CInt]]
   --------
   [⊢ [_ ≫ (ro:vector-ref v- i-) ⇒ : τ]]]
  [(_ v:expr i:expr) ≫
   [⊢ [v ≫ v- ⇒ : (~or (~CMVectorof τ) (~CIVectorof τ))]]
   [⊢ [i ≫ i- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:vector-ref v- i-) ⇒ : #,(type-merge #'τ #'τ)]]]
  [(_ v:expr i:expr) ≫
   [⊢ [v ≫ v- ⇒ : (~U* (~and (~or (~CMVectorof τ) (~CIVectorof τ))) ...)]]
   [⊢ [i ≫ i- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:vector-ref v- i-) ⇒ : #,(type-merge* #'[τ ...])]]])

(define-typed-syntax vector-set!
  [(_ v:expr i:expr x:expr) ≫
   [⊢ v ≫ v- ⇒ (~CMVectorof τ)]
   [⊢ i ≫ i- ⇐ Nat]
   [⊢ x ≫ x- ⇐ τ]
   --------
   [⊢ (ro:vector-set! v- i- x-) ⇒ CUnit]])

;; ------------------------------------------------------------------------

(provide vector->list list->vector)

(define-typed-syntax vector->list
  [(_ v:expr) ≫
   [⊢ v ≫ v- ⇒ (~CMVectorof τ)]
   --------
   [⊢ (ro:vector->list v-) ⇒ (CListof τ)]])

;; TODO: add CList case?
;; returne mutable vector
(define-typed-syntax list->vector
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:list->vector ⇒ : (Ccase-> (C→ (CListof Any) (CMVectorof Any))
                                        (C→ (Listof Any) (MVectorof Any)))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (CMVectorof #,(if (concrete? #'τ) #'(U τ) #'τ))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   #:with [τ* ...] (stx-map (λ (τ) (if (concrete? τ) #`(U #,τ) τ)) #'[τ ...])
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (U (CMVectorof τ*) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ ...)]]
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (CMVectorof (U τ ...))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (U (CMVector (U τ ...)) ...)]]])

;; ------------------------------------------------------------------------

