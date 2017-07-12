#lang turnstile

(require typed/rosette/types
         (prefix-in ro: rosette)
         (postfix-in - rosette))

;; ------------------------------------------------------------------------

(provide (typed-out [vector? : LiftedPred]))

(provide vector
         vector-immutable
         make-vector
         make-immutable-vector
         build-vector
         build-immutable-vector
         vector-length
         vector-ref
         vector-set!
         vector->list
         list->vector)

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

(define-typed-syntax vector-length
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~or (~CMVectorof _) (~CIVectorof _))]
   --------
   [⊢ (ro:vector-length e-) ⇒ CNat]]
  [(_ e n) ≫
   [⊢ e ≫ e- ⇒ (~U* (~and (~or (~CMVectorof τ) (~CIVectorof τ))) ...)]
   --------
   [⊢ [_ ≫ (ro:vector-length e-) ⇒ Nat]]])

(define-typed-syntax vector-set!
  [(_ v:expr i:expr x:expr) ≫
   [⊢ v ≫ v- ⇒ (~CMVectorof τ)]
   [⊢ i ≫ i- ⇐ Int]
   [⊢ x ≫ x- ⇐ τ]
   --------
   [⊢ (ro:vector-set! v- i- x-) ⇒ CUnit]])

;; ------------------------------------------------------------------------

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
;; not in rosette/safe

(define-typed-syntax make-vector
  [(_ size:expr v:expr) ≫
   [⊢ size ≫ size- ⇐ CNat]
   [⊢ v ≫ v- ⇒ τ]
   --------
   [⊢ (ro:make-vector size- v-) ⇒ #,(syntax/loc this-syntax (CMVectorof τ))]])

;; programmer cannot manually do (vector->immutable-vector (make-vector ...))
;; bc there might be an intermediate mutable vector with non-symbolic elements
(define-typed-syntax make-immutable-vector
  [(_ n v) ≫
   [⊢ n ≫ n- ⇐ CNat]
   [⊢ v ≫ v- ⇒ τ]
   --------
   [⊢ (vector->immutable-vector- (make-vector- n- v-)) ⇒ (CIVectorof τ)]])

(define-typed-syntax build-vector
  [(_ n f) ≫
   [⊢ n ≫ n- ⇐ CNat]
   [⊢ f ≫ f- ⇒ (~C→ CNat τ_out)]
   --------
   [⊢ (build-vector- n- f-) ⇒ #,(syntax/loc this-syntax (CMVectorof τ_out))]])

(define-typed-syntax build-immutable-vector
  [(_ n f) ≫
   [⊢ n ≫ n- ⇐ CNat]
   [⊢ f ≫ f- ⇒ (~C→ CNat τ_out)]
   --------
   [⊢ (vector->immutable-vector- (build-vector- n- f-)) ⇒ (CIVectorof τ_out)]])
