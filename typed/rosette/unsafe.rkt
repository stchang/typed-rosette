#lang turnstile

(require typed/rosette/types
         (prefix-in ro: rosette))

(provide unsafe-assign-type
         unsafe-define/assign-type
         unsafe-cast-concrete
         unsafe-cast-nonfalse)

;; Unsafely assigning types to values

;; unsafe-assign-type doesn't typecheck anything within the expression
(define-typed-syntax unsafe-assign-type
  #:datum-literals [:]
  [(_ e:expr : τ:expr) ≫
   --------
   [⊢ (ro:#%expression e) ⇒ : τ]])

(define-syntax-parser unsafe-define/assign-type
  #:datum-literals [:]
  [(_ x:id : τ:expr e:expr)
   #'(define x (unsafe-assign-type e : τ))])

(define-typed-syntax unsafe-cast-concrete
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~U* (~Term* ty))]
   --------
   [⊢ e- ⇒ (CU ty)]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~U* ty ...)]
   --------
   [⊢ e- ⇒ (CU ty ...)]])

(define-typed-syntax unsafe-cast-nonfalse
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~CU* ~CFalse ... (~and (~not ~CFalse) ty) ... ~CFalse ...)]
   --------
   [⊢ e- ⇒ (CU ty ...)]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~U* ~CFalse ... (~and (~not ~CFalse) ty) ... ~CFalse ...)]
   --------
   [⊢ e- ⇒ (U ty ...)]])
