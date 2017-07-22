#lang turnstile

(require typed/rosette/types
         (prefix-in ro: rosette))

(provide unsafe-assign-type
         unsafe-define/assign-type
         unsafe-cast-concrete
         unsafe-cast-nonfalse
         unsafe-strip-term
         untyped-let
         untyped-begin)

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
   [⊢ e ≫ e- ⇒ (~CU* (~and (~not ~CFalse) ty1) ... ~CFalse
                     (~and (~not ~CFalse) ty2) ...)]
   --------
   [⊢ e- ⇒ (CU ty1 ... ty2 ...)]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~U* (~and (~not ~CFalse) ty1) ... ~CFalse
                    (~and (~not ~CFalse) ty2) ...)]
   --------
   [⊢ e- ⇒ (U ty1 ... ty2 ...)]]
  [(_ e) ≫ --- [≻ e]])

(define-typed-syntax unsafe-strip-term
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~Term* τ)]
   ------------------------
   [⊢ e- ⇒ : τ]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~U* (~or (~Term* ty1) ty2) ...)]
   ------------------------
   [⊢ e- ⇒ : (U ty1 ... ty2 ...)]])
   
;; untyped passthroughs --------------------------------------------------

(define-typed-syntax (untyped-let () . args) ≫
  ---------
  [⊢ (begin- . args) ⇒ Any])

(define-typed-syntax (untyped-begin . args) ≫
  ---------
  [⊢ (begin- . args) ⇒ Any])
