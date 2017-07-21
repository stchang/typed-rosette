#lang turnstile
;; reuse unlifted forms as-is
(reuse  
 let* letrec #%datum ann current-join ⊔
 define-type-alias define-named-type-alias
 #:from turnstile/examples/stlc+union)
(require
 ;; manual imports
 (only-in turnstile/examples/stlc+union
          define-named-type-alias)
 ;; import typed rosette types
 "rosette/types.rkt"
 ;; import base forms
 (rename-in (except-in "rosette/base-forms.rkt" list) [#%app app])
 (except-in "rosette/bool.rkt" and or not)
 (except-in "rosette/list.rkt" pair)
 "rosette/match-core.rkt"
 "rosette/match-pat-forms.rkt"
 "rosette/struct.rkt"
 "rosette/struct-type-properties.rkt"
 "rosette/generic-interfaces.rkt"
 "rosette/for-forms.rkt"
 "rosette/format.rkt"
 "rosette/vector.rkt"
 "rosette/set.rkt"
 "rosette/hash.rkt"
 "rosette/function.rkt"
 "rosette/unsafe.rkt"
 ;; base lang
 (prefix-in ro: (combine-in rosette rosette/lib/synthax
                            "rosette/concrete-predicate.rkt"))
 (rename-in "rosette-util.rkt" [bitvector? lifted-bitvector?]))

(provide : define define/conc set! λ λ/conc apply ann begin
         let
         (rename-out [app #%app]
                     [ro:#%module-begin #%module-begin] 
                     [λ lambda]
                     [λ/conc lambda/conc]
                     [ro:begin splicing-begin])
         match match-let _ var ?
         (all-from-out "rosette/bool.rkt"
                       "rosette/match-pat-forms.rkt"
                       "rosette/struct.rkt"
                       "rosette/struct-type-properties.rkt"
                       "rosette/generic-interfaces.rkt"
                       "rosette/for-forms.rkt"
                       "rosette/format.rkt"
                       "rosette/list.rkt"
                       "rosette/vector.rkt"
                       "rosette/set.rkt"
                       "rosette/hash.rkt"
                       "rosette/function.rkt"
                       "rosette/unsafe.rkt")
         (for-syntax get-pred expand/ro concrete?)
         define-typed-param
         CAnyDeep CAny Any CNothing Nothing
         Term
         CU U (for-syntax ~CU* ~U*)
         Constant Solvable
         Struct
         C→ C→* C→/conc C→** → →/conc (for-syntax ~C→ ~C→* ~C→/conc ~C→** C→?
                                                  concrete-function-type?)
         Ccase-> (for-syntax ~Ccase-> Ccase->?) ; TODO: sym case-> not supported
         CListof Listof CList CPair Pair
         (for-syntax ~CListof)
         CVectorof MVectorof IVectorof Vectorof CMVectorof CIVectorof CVector
         CParamof ; TODO: symbolic Param not supported yet
         CISetof CMSetof
         CBoxof MBoxof IBoxof CMBoxof CIBoxof CHashTable
         (for-syntax ~CMVectorof ~CMSetof ~CHashTable)
         CUnit Unit (for-syntax ~CUnit CUnit?)
         CNegInt NegInt
         CZero Zero
         CPosInt PosInt
         CNat Nat
         CInt Int
         CFloat Float
         CNum Num
         CFalse CTrue CBool False True Bool
         CString String (for-syntax CString?)
         CStx ; symblic Stx not supported
         CSymbol
         CAsserts
         ;; BV types
         CBV BV
         CBVPred BVPred
         CSolution CSolver CPict CRegexp
         LiftedPred LiftedPred2 LiftedNumPred LiftedIntPred UnliftedPred)


;; a legacy auto-providing version of define-typed-syntax
;; TODO: convert everything to new define-typed-syntax
(define-syntax (define-typed-syntax stx)
  (syntax-parse stx
    [(_ name:id #:export-as out-name:id . rst)
     #'(begin-
         (provide- (rename-out [name out-name]))
         (define-typerule name . rst))] ; define-typerule doesnt provide
    [(_ name:id . rst)
     #'(define-typed-syntax name #:export-as name . rst)]
    [(_ (name:id . pat) . rst)
     #'(define-typed-syntax name #:export-as name [(_ . pat) . rst])]))

;; ---------------------------------
;; define-typed-param
(define-syntax (define-typed-param stx)
  (syntax-parse stx
    [(_ name:id (~datum :) ty)
     #:with uname ((current-host-lang) #'name) ; untyped
     #'(define-typed-syntax name
         [_:id  ≫ --- [⊢ uname ⇒ (CParamof ty)]]
         [(_)   ≫ --- [⊢ (uname) ⇒ ty]]
         [(_ e) ≫
          [⊢ e ≫ e- ⇒ _]
          #:when (false? (typeof #'e-)) ; allow usage in untyped code
          --------
          [⊢ (uname e-) ⇒ CUnit]]
         [(_ e) ≫
          [⊢ e ≫ e- ⇐ ty]
          --------
          [⊢ (uname e-) ⇒ CUnit]])]))

;; ---------------------------------
;; define-symbolic

(define-typed-syntax define-symbolic
  [(_ x:id ...+ pred?) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   #:with (y ...) (generate-temporaries #'(x ...))
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : (Constant ty)))) ...
          (ro:define-symbolic y ... pred?-))]])

(define-typed-syntax define-symbolic*
  [(_ x:id ...+ pred?) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   #:with (y ...) (generate-temporaries #'(x ...))
   --------
   [_ ≻ (begin-
          (define-syntax- x (make-rename-transformer (⊢ y : (Constant ty)))) ...
          (ro:define-symbolic* y ... pred?-))]])

;; TODO: support internal definition contexts
(define-typed-syntax let-symbolic
  [(_ (x:id ...+ pred?) e ...) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   [([x ≫ x- : (Constant ty)] ...) ⊢ [(begin e ...) ≫ e- ⇒ τ_out]]
   --------
   [⊢ [_ ≫ (ro:let-values
            ([(x- ...) (ro:let ()
                         (ro:define-symbolic x ... pred?-)
                         (ro:values x ...))])
            e-) ⇒ : τ_out]]])
(define-typed-syntax let-symbolic*
  [(_ (x:id ...+ pred?) e ...) ≫
   [⊢ [pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?)]]
   #:fail-unless (syntax-e #'s?)
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'pred?))
   [([x ≫ x- : (Constant ty)] ...) ⊢ [(begin e ...) ≫ e- ⇒ τ_out]]
   --------
   [⊢ [_ ≫ (ro:let-values
            ([(x- ...) (ro:let ()
                         (ro:define-symbolic* x ... pred?-)
                         (ro:values x ...))])
            e-) ⇒ : τ_out]]])

;; ---------------------------------
;; assert, assert-type

(define-typed-syntax assert
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:assert e-) ⇒ : CUnit]]]
  [(_ e m) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   [⊢ [m ≫ m- ⇐ : (CU CString (C→ CNothing))]]
   --------
   [⊢ [_ ≫ (ro:assert e- m-) ⇒ : CUnit]]])

;; TODO: assert-type wont work with unlifted types
;; but sometimes it should, eg in with for/all lifted functions
;; - but this means we need to lift a pred (eg string?) and associate it with the newly lifted type 
(define-typed-syntax assert-type #:datum-literals (:)
  [(_ e : ty:type) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   #:with pred (get-pred #'ty.norm)
   #:fail-when (and (not (syntax-e #'pred)) #'ty)
   "type does not (or cannot) have an associated predicate"
   --------
   [⊢ [_ ≫ (ro:#%app assert-pred e- pred) ⇒ : ty.norm]]])  


;; ---------------------------------
;; Racket forms

;; TODO: get subtyping to work for struct-generated types?
;; TODO: handle mutable structs properly
#;(define-typed-syntax struct #:datum-literals (:)
  [(_ name:id (x:id ...) ~! . rst) ≫
   #:fail-when #t "Missing type annotations for fields"
   --------
   [_ ≻ (ro:struct name (x ...) . rst)]]
  [(_ name:id ([x:id : ty:type] ...) . kws) ≫
   #:fail-unless (id-lower-case? #'name)
                 (format "Expected lowercase struct name, given ~a" #'name)
   #:with name* (generate-temporary #'name)
   #:with Name (id-upcase #'name)
   #:with CName (format-id #'name "C~a" #'Name)
   #:with TyOut #'(Name ty ...)
   #:with CTyOut #'(CName ty ...)
   #:with (name-x ...) (stx-map (lambda (f) (format-id #'name "~a-~a" #'name f)) #'(x ...))
   #:with (name-x* ...) (stx-map (lambda (f) (format-id #'name* "~a-~a" #'name* f)) #'(x ...))
   #:with name? (format-id #'name "~a?" #'name)
   #:with name?* (format-id #'name* "~a?" #'name*)
   --------
   [_ ≻ (ro:begin
          (ro:struct name* (x ...) . kws)
          (define-type-constructor CName #:arity = #,(stx-length #'(x ...)))
          (define-named-type-alias (Name x ...) (U (CName x ...)))
          (define-syntax name   ; constructor
            (make-variable-like-transformer 
             (assign-type #'name* #'(C→ ty ... CTyOut))))
          (define-syntax name?  ; predicate
            (make-variable-like-transformer 
             (assign-type #'name?* #'LiftedPred)))
          (define-syntax name-x ; accessors
            (make-variable-like-transformer 
             (assign-type #'name-x* #'(C→ TyOut ty)))) ...)]])

;; TODO: add type rules for generics
#;(define-typed-syntax define-generics #:datum-literals (: ->)
  [(_ name:id (f:id x:id ... -> ty-out)) ≫
   #:with app-f (format-id #'f "apply-~a" #'f)
   --------
   [_ ≻ (ro:begin
         (ro:define-generics name (f x ...))
         (define-syntax app-f ; tmp workaround: each gen fn has its own apply
           (syntax-parser
             [(_ . es)
              #:with es+ (stx-map expand/df #'es)
              (assign-type #'(ro:#%app f . es+) #'ty-out)])))]])

;; ---------------------------------
;; hash tables

(define-typed-syntax hash-keys
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CHashTable τ _)]]
   --------
   [⊢ [_ ≫ (ro:hash-keys e-) ⇒ : (CListof τ)]]])

(define-typed-syntax hash-values
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CHashTable _ τ)]]
   --------
   [⊢ [_ ≫ (ro:hash-values e-) ⇒ : (CListof τ)]]])

;; ---------------------------------
;; lists



;; n must be Int bc Rosette does not have symbolic Nats
(define-typed-syntax take
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:take ⇒ : (Ccase-> (C→ (CListof Any) CInt (CListof Any))
                                (C→ (Listof Any) Int (Listof Any)))]]]
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:take e- n-) ⇒ : (CListof τ)]]]
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:take e- n-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ ...)]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:take e- n-) ⇒ : (CListof (U τ ...))]]]
  [(_ e n) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ ...) ...)]]
   [⊢ [n ≫ n- ⇐ : Int]]
   --------
   [⊢ [_ ≫ (ro:take e- n-) ⇒ : (U (CList (U τ ...)) ...)]]])

(define-typed-syntax reverse
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:reverse ⇒ : (Ccase-> (C→ (CListof Any) (CListof Any))
                                   (C→ (Listof Any) (Listof Any)))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:reverse e-) ⇒ : (CListof τ)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:reverse e-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList . τs)]]
   #:with τs/rev (stx-rev #'τs)
   --------
   [⊢ [_ ≫ (ro:reverse e-) ⇒ : (CList . τs/rev)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList . τs) ...)]]
   #:with (τs/rev ...) (stx-map stx-rev #'(τs ...))
   --------
   [⊢ [_ ≫ (ro:reverse e-) ⇒ : (U (CList . τs/rev) ...)]]])

;; ---------------------------------
;; IO and other built-in ops

(provide (typed-out [void : (C→* [] [] #:rest (Listof Any) CUnit)]
                    [display : (C→ Any CUnit)]
                    [displayln : (C→ Any CUnit)]
                    [with-output-to-string : (C→ (C→ Any) CString)]
                    [string-contains? : (C→ CString CString CBool)]
                    [pretty-print : (C→ Any CUnit)]
                    
                    [string-length : (C→ CString CNat)]
                    [string-append : (C→ CString CString CString)]

                    [equal? : LiftedPredDeep2]
                    [eq? : LiftedPredDeep2]
                    [distinct? : (Ccase-> (C→* [] [] #:rest (CListof CAny) CBool)
                                          (C→* [] [] #:rest (CListof Any) Bool)
                                          (C→* [] [] #:rest (Listof Any) Bool))]
                    
                    [pi : CNum]
                    
                    [add1 : (Ccase-> (C→ CNegInt (CU CNegInt CZero))
                                     (C→ NegInt (U NegInt Zero))
                                     (C→ CZero CPosInt)
                                     (C→ Zero PosInt)
                                     (C→ CPosInt CPosInt)
                                     (C→ PosInt PosInt)
                                     (C→ CNat CPosInt)
                                     (C→ Nat PosInt)
                                     (C→ CInt CInt)
                                     (C→ Int Int))]
                    [sub1 : (Ccase-> (C→ CNegInt CNegInt)
                                     (C→ NegInt NegInt)
                                     (C→ CZero CNegInt)
                                     (C→ Zero NegInt)
                                     (C→ CPosInt CNat)
                                     (C→ PosInt Nat)
                                     (C→ CNat CInt)
                                     (C→ Nat Int)
                                     (C→ CInt CInt)
                                     (C→ Int Int))]
                    [+ : (Ccase-> (C→ CZero)
                                  (C→* [] [] #:rest (CListof CNat) CNat)
                                  (C→* [] [] #:rest (CListof Nat) Nat)
                                  (C→* [] [] #:rest (Listof Nat) Nat)
                                  (C→* [] [] #:rest (CListof CInt) CInt)
                                  (C→* [] [] #:rest (CListof Int) Int)
                                  (C→* [] [] #:rest (Listof Int) Int)
                                  (C→* [] [] #:rest (CListof CNum) CNum)
                                  (C→* [] [] #:rest (CListof Num) Num)
                                  (C→* [] [] #:rest (Listof Num) Num))]
                    [- : (Ccase-> (C→ CInt CInt)
                                  (C→ CInt CInt CInt)
                                  (C→ CInt CInt CInt CInt)
                                  (C→ CInt CInt CInt CInt CInt)
                                  (C→ Int Int Int)
                                  (C→ Int Int Int Int)
                                  (C→ Int Int Int Int Int)
                                  (C→ CNum CNum CNum)
                                  (C→ CNum CNum CNum CNum)
                                  (C→ CNum CNum CNum CNum CNum)
                                  (C→ Num Num Num)
                                  (C→ Num Num Num Num)
                                  (C→ Num Num Num Num Num))]
                    [* : (Ccase-> (C→ CNat CNat CNat)
                                  (C→ CNat CNat CNat CNat)
                                  (C→ CNat CNat CNat CNat CNat)
                                  (C→ Nat Nat Nat)
                                  (C→ Nat Nat Nat Nat)
                                  (C→ Nat Nat Nat Nat Nat)
                                  (C→ CInt CInt CInt)
                                  (C→ CInt CInt CInt CInt)
                                  (C→ CInt CInt CInt CInt CInt)
                                  (C→ Int Int Int)
                                  (C→ Int Int Int Int)
                                  (C→ Int Int Int Int Int)
                                  (C→ CNum CNum CNum)
                                  (C→ CNum CNum CNum CNum)
                                  (C→ CNum CNum CNum CNum CNum)
                                  (C→ Num Num Num)
                                  (C→ Num Num Num Num)
                                  (C→ Num Num Num Num Num))]
                    [/ : (Ccase-> (C→ CNum CNum)
                                  (C→ CNum CNum CNum)
                                  (C→ CNum CNum CNum CNum)
                                  (C→ Num Num)
                                  (C→ Num Num Num)
                                  (C→ Num Num Num Num))]
                    [= : (Ccase-> (C→ CNum CNum CBool)
                                  (C→ CNum CNum CNum CBool)
                                  (C→ Num Num Bool)
                                  (C→ Num Num Num Bool))]
                    [< : (Ccase-> (C→ CNum CNum CBool)
                                  (C→ CNum CNum CNum CBool)
                                  (C→ Num Num Bool)
                                  (C→ Num Num Num Bool))]
                    [> : (Ccase-> (C→ CNum CNum CBool)
                                  (C→ CNum CNum CNum CBool)
                                  (C→ Num Num Bool)
                                  (C→ Num Num Num Bool))]
                    [<= : (Ccase-> (C→ CNum CNum CBool)
                                   (C→ CNum CNum CNum CBool)
                                   (C→ Num Num Bool)
                                   (C→ Num Num Num Bool))]
                    [>= : (Ccase-> (C→ CNum CNum CBool)
                                   (C→ CNum CNum CNum CBool)
                                   (C→ Num Num Bool)
                                   (C→ Num Num Num Bool))]
                    
                    [abs : (Ccase-> (C→ CPosInt CPosInt)
                                    (C→ PosInt PosInt)
                                    (C→ CZero CZero)
                                    (C→ Zero Zero)
                                    (C→ CNegInt CPosInt)
                                    (C→ NegInt PosInt)
                                    (C→ CInt CInt)
                                    (C→ Int Int)
                                    (C→ CNum CNum)
                                    (C→ Num Num))]
                    
                    [max : (Ccase-> (C→ CInt CInt CInt)
                                    (C→ CInt CInt CInt CInt)
                                    (C→ CNum CNum CNum)
                                    (C→ CNum CNum CNum CNum)
                                    (C→ Int Int Int)
                                    (C→ Int Int Int Int)
                                    (C→ Num Num Num)
                                    (C→ Num Num Num Num))]
                    [min : (Ccase-> (C→ CInt CInt CInt)
                                    (C→ CInt CInt CInt CInt)
                                    (C→ CNum CNum CNum)
                                    (C→ CNum CNum CNum CNum)
                                    (C→ Int Int Int)
                                    (C→ Int Int Int Int)
                                    (C→ Num Num Num)
                                    (C→ Num Num Num Num))] 
                    ;; out type for these fns must be CNum, because of +inf.0 and +nan.0
                    [floor : (Ccase-> (C→ CNum CNum)
                                      (C→ Num Num))]
                    [ceiling : (Ccase-> (C→ CNum CNum)
                                        (C→ Num Num))]
                    [truncate : (Ccase-> (C→ CNum CNum)
                                         (C→ Num Num))]
                    [exact-round : (Ccase-> (C→ CNat CNat)
                                            (C→ Nat Nat)
                                            (C→ CNum CInt)
                                            (C→ Num Int))]
                    [exact-floor : (Ccase-> (C→ CNat CNat)
                                            (C→ Nat Nat)
                                            (C→ CNum CInt)
                                            (C→ Num Int))]
                    [exact-ceiling : (Ccase-> (C→ CNat CNat)
                                              (C→ Nat Nat)
                                              (C→ CNum CInt)
                                              (C→ Num Int))]
                    
                    [sgn : (Ccase-> (C→ CZero CZero)
                                    (C→ Zero Zero)
                                    (C→ CInt CInt)
                                    (C→ Int Int)
                                    (C→ CNum CNum)
                                    (C→ Num Num))]
                    
                    [expt : (Ccase-> (C→ CNum CZero CPosInt)
                                     (C→ Num Zero PosInt)
                                     (C→ CNat CNat CNat)
                                     (C→ Nat Nat Nat)
                                     (C→ CInt CInt CInt)
                                     (C→ Int Int Int)
                                     (C→ CNum CNum CNum)
                                     (C→ Num Num Num))]

                    [exp : (C→ CNum CNum)]
                    [log : (C→ CNum CNum)]
                    
                    [real->integer : (C→ Num Int)]
                    [string? : (UnliftedPredFor CString)]
                    [number? : (LiftedPredFor Num)]
                    [positive? : LiftedNumPred]
                    [negative? : LiftedNumPred]
                    [zero? : LiftedNumPred]
                    [even? : LiftedIntPred]
                    [odd? : LiftedIntPred]
                    [exact-nonnegative-integer? : (LiftedPredFor Nat)]

                    [inexact->exact : (Ccase-> (C→ CNum CNum)
                                               (C→ Num Num))]
                    [exact->inexact : (Ccase-> (C→ CNum CNum)
                                               (C→ Num Num))]
                    [quotient : (Ccase-> (C→ CNat CNat CNat)
                                         (C→ CInt CInt CInt)
                                         (C→ Int Int Int))]
                    [remainder : (Ccase-> (C→ CNat CNat CNat)
                                          (C→ CInt CInt CInt)
                                          (C→ Int Int Int))]
                    [modulo : (Ccase-> (C→ CNat CNat CNat)
                                       (C→ CInt CInt CInt)
                                       (C→ Int Int Int))]
                    ;; not in rosette/safe
                    [random : (C→ CNat CNat)]
                    ;; rosette-specific
                    [pc : (C→ Bool)]
                    [asserts : (C→ CAsserts)]
                    [clear-asserts! : (C→ CUnit)]))

;; ---------------------------------
;; more built-in ops

(define-simple-macro
  (define-solvable-type-predicate pred? ro-pred? CType Type)
  (begin-
    (provide- pred?)
    (define-syntax- pred?
      (make-variable-like-transformer
       (attach (⊢ (mark-solvablem ro-pred?) : (LiftedPredFor Type))
               'typefor
               ((current-type-eval) #'(Term CType)))))))

;(define-rosette-primop boolean? : (C→ Any Bool))
(define-solvable-type-predicate boolean? ro:boolean? CBool Bool)

;(define-rosette-primop integer? : (C→ Any Bool))
(define-solvable-type-predicate integer? ro:integer? CInt Int)

;(define-rosette-primop real? : (C→ Any Bool))
(define-solvable-type-predicate real? ro:real? CNum Num)

(provide (typed-out [concrete-boolean?
                     : (C→* [Any] [] CBool :
                            #:+ (@ 0 : CBool) #:- (!@ 0 : CBool))]))

(define-typed-syntax time
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : ty]]
   --------
   [⊢ [_ ≫ (ro:time e-) ⇒ : ty]]])

;; ---------------------------------
;; mutable boxes

(define-typed-syntax box
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : τ]]
   --------
   [⊢ [_ ≫ (ro:box e-) ⇒ : (CMBoxof #,(type-merge #'τ #'τ))]]])

(define-typed-syntax box-immutable
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : τ]]
   --------
   [⊢ [_ ≫ (ro:box-immutable e-) ⇒ : (CIBoxof τ)]]])

(define-typed-syntax unbox
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~or (~CMBoxof τ) (~CIBoxof τ))]]
   --------
   [⊢ [_ ≫ (ro:unbox e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~and (~or (~CMBoxof τ) (~CIBoxof τ))) ...)]]
   #:with τ_out (type-merge* #'[τ ...])
   --------
   [⊢ [_ ≫ (ro:unbox e-) ⇒ : τ_out]]])

;; TODO: implement multiple values
;; result type should be (Valuesof ty CAsserts)
(define-typed-syntax with-asserts
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : ty]]
   --------
   [⊢ [_ ≫ (ro:with-asserts e-) ⇒ : ty]]])

(provide (typed-out
          [term-cache
           : (Ccase-> (C→ (CHashTable Any Any))
                      (C→ (CHashTable Any Any) CUnit))]
          [clear-terms! 
           : (Ccase-> (C→ CUnit)
                      (C→ CFalse CUnit)
                      (C→ (CListof Any) CUnit))] ; list of terms
          [clear-state! : (C→ CUnit)]))

;; ---------------------------------
;; BV Types and Operations

;; this must be a macro in order to support Racket's overloaded set/get
;; parameter patterns
(define-typed-syntax current-bitwidth
  [_:id ≫
   --------
   [⊢ [_ ≫ ro:current-bitwidth ⇒ : (CParamof (CU CFalse CPosInt))]]]
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:current-bitwidth) ⇒ : (CU CFalse CPosInt)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇐ : (CU CFalse CPosInt)]]
   --------
   [⊢ [_ ≫ (ro:current-bitwidth e-) ⇒ : CUnit]]])

(define-named-type-alias BVMultiArgOp (Ccase-> (C→ BV BV BV)
                                               (C→ BV BV BV BV)))

(provide (typed-out [bv : (Ccase-> (C→ CInt CBVPred CBV)
                                   (C→ CInt CPosInt CBV))]
                    [bv? : (LiftedPredFor BV)]
                    
                    [bveq : (C→ BV BV Bool)]
                    [bvslt : (C→ BV BV Bool)]
                    [bvult : (C→ BV BV Bool)]
                    [bvsle : (C→ BV BV Bool)]
                    [bvule : (C→ BV BV Bool)]
                    [bvsgt : (C→ BV BV Bool)]
                    [bvugt : (C→ BV BV Bool)]
                    [bvsge : (C→ BV BV Bool)]
                    [bvuge : (C→ BV BV Bool)]
                    
                    [bvnot : (C→ BV BV)]
                    
                    [bvand : (C→ BV BV BV)]
                    [bvor : (C→ BV BV BV)]
                    [bvxor : (C→ BV BV BV)]
                    
                    [bvshl : (C→ BV BV BV)]
                    [bvlshr : (C→ BV BV BV)]
                    [bvashr : (C→ BV BV BV)]
                    [bvneg : (C→ BV BV)]
                    
                    [bvadd : BVMultiArgOp]
                    [bvsub : BVMultiArgOp]
                    [bvmul : BVMultiArgOp]
                    
                    [bvsdiv : (C→ BV BV BV)]
                    [bvudiv : (C→ BV BV BV)]
                    [bvsrem : (C→ BV BV BV)]
                    [bvurem : (C→ BV BV BV)]
                    [bvsmod : (C→ BV BV BV)]
                    
                    [concat : BVMultiArgOp]
                    [extract : (C→ Int Int BV BV)]
                    [sign-extend : (C→ BV BVPred BV)]
                    [zero-extend : (C→ BV BVPred BV)]
                    
                    [bitvector->integer : (C→ BV Int)]
                    [bitvector->natural : (C→ BV Nat)]
                    [integer->bitvector : (C→ Int BVPred BV)]
                    
                    [bitvector-size : (C→ CBVPred CPosInt)]))

;(define-rosette-primop bitvector : (C→ CPosInt CBVPred))
(define-typed-syntax bitvector
  [_:id ≫
   --------
   [⊢ ro:bitvector ⇒ (C→ CPosInt CBVPred)]]
  [(_ n) ≫
   [⊢ n ≫ n- ⇐ CPosInt]
   --------
   [⊢ (mark-solvablem
       (ro:bitvector n-))
      (⇒ : CBVPred)
      (⇒ typefor (Term CBV))]])

;; bitvector? can produce type CFalse if input does not have type (C→ Any Bool)
;; result is always CBool, since anything symbolic returns false
;(define-rosette-primop bitvector? : (C→ Any Bool))
(define-typed-syntax bitvector?
  [_:id ≫
   --------
   [⊢ ro:bitvector? ⇒ UnliftedPred]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇐ LiftedPred]
   --------
   [⊢ (ro:bitvector? e-) ⇒ CBool]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ _]
   --------
   [⊢ (ro:bitvector? e-) ⇒ CFalse]])

;; ---------------------------------
;; Uninterpreted functions

(define-typed-syntax ~>
  [(_ pred? ...+ out) ≫
   [⊢ pred? ≫ pred?- (⇒ : _) (⇒ typefor ty) (⇒ solvable? s?) (⇒ function? f?)] ...
   [⊢ out ≫ out- (⇒ : _) (⇒ typefor ty-out) (⇒ solvable? out-s?) (⇒ function? out-f?)]
   #:fail-unless (stx-andmap syntax-e #'(s? ... out-s?))
                 (format "Expected a Rosette-solvable type, given ~a." 
                         (syntax->datum #'(pred? ... out)))
   #:fail-when (stx-ormap syntax-e #'(f? ... out-f?))
               (format "Expected a non-function Rosette type, given ~a." 
                       (syntax->datum #'(pred? ... out)))
   --------
   [⊢ (mark-solvablem
       (mark-functionm
        (ro:~> pred?- ... out-)))
      (⇒ : LiftedPred)
      (⇒ typefor (Term (C→ (U ty) ... ty-out)))]])

(provide (typed-out [fv? : LiftedPred]))

;; function? can produce type CFalse if input does not have type (C→ Any Bool)
;; result is always CBool, since anything symbolic returns false
;(define-rosette-primop function? : (C→ Any Bool))
(define-typed-syntax function?
  [_:id ≫
   --------
   [⊢ ro:function? ⇒ UnliftedPred]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇐ LiftedPred]
   --------
   [⊢ (ro:function? e-) ⇒ CBool]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ _]
   --------
   [⊢ (ro:function? e-) ⇒ CFalse]])

;; ---------------------------------
;; Logic operators
(provide (typed-out [! : (C→ Bool Bool)]
                    [<=> : (C→ Bool Bool Bool)]
                    [=> : (C→ Bool Bool Bool)]))

(define-typed-syntax &&
  [_:id ≫
   --------
   [⊢ [_ ≫ ro:&& ⇒ :
         (C→* [] [] #:rest (Listof Bool) Bool)]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇐ : Bool] ...]
   --------
   [⊢ [_ ≫ (ro:&& e- ...) ⇒ : Bool]]])
(define-typed-syntax ||
  [_:id ≫
   --------
   [⊢ [_ ≫ ro:|| ⇒ :
           (C→* [] [] #:rest (Listof Bool) Bool)]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇐ : Bool] ...]
   --------
   [⊢ [_ ≫ (ro:|| e- ...) ⇒ : Bool]]])

;; and, or, and not are defined in rosette/forms-pre-match.rkt

(define-typed-syntax nand
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:nand) ⇒ : CFalse]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : _] ...]
   --------
   [⊢ [_ ≫ (ro:nand e- ...) ⇒ : Bool]]])
(define-typed-syntax nor
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:nor) ⇒ : CTrue]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : _] ...]
   --------
   [⊢ [_ ≫ (ro:nor e- ...) ⇒ : Bool]]])
(define-typed-syntax implies
  [(_ e1 e2) ≫
   --------
   [_ ≻ (if e1 e2 (stlc+union:#%datum . #t))]])

;; ---------------------------------
;; solver forms

(provide (typed-out [sat? : UnliftedPred]
                    [unsat? : UnliftedPred]
                    [solution? : (UnliftedPredFor CSolution)]
                    [unknown? : UnliftedPred]
                    [sat : (Ccase-> (C→ CSolution)
                                    (C→ (CHashTable Any Any) CSolution))]
                    [unsat : (Ccase-> (C→ CSolution)
                                      (C→ (CListof Bool) CSolution))]
                    [unknown : (C→ CSolution)]
                    [model : (C→ CSolution (CHashTable Any Any))]
                    [core : (C→ CSolution (U (Listof Any) CFalse))]))

;(define-rosette-primop forall : (C→ (CListof Any) Bool Bool))
;(define-rosette-primop exists : (C→ (CListof Any) Bool Bool))
(define-typed-syntax forall
  [(_ vs body) ≫
   ;; TODO: allow U of Constants?
   [⊢ [vs ≫ vs- ⇒ : (~CListof ~! ty)]]
   #:fail-unless (Constant*? #'ty)
   (format "Expected list of symbolic constants, given list of ~a" 
           (type->str #'ty))
   [⊢ [body ≫ body- ⇐ : Bool]]
   --------
   [⊢ [_ ≫ (ro:forall vs- body-) ⇒ : Bool]]]
  [(_ vs body) ≫
   [⊢ [vs ≫ vs- ⇒ : (~CList ~! ty ...)]]
   #:fail-unless (stx-andmap Constant*? #'(ty ...))
   (format "Expected list of symbolic constants, given list containing: ~a" 
           (string-join (stx-map type->str #'(ty ...)) ", "))
   [⊢ [body ≫ body- ⇐ : Bool]]
   --------
   [⊢ [_ ≫ (ro:forall vs- body-) ⇒ : Bool]]])
(define-typed-syntax exists
  [(_ vs body) ≫
   [⊢ [vs ≫ vs- ⇒ : (~CListof ~! ty)]]
   ;; TODO: allow U of Constants?
   #:fail-unless (Constant*? #'ty)
   (format "Expected list of symbolic constants, given list of ~a" 
           (type->str #'ty))
   [⊢ [body ≫ body- ⇐ : Bool]]
   --------
   [⊢ [_ ≫ (ro:exists vs- body-) ⇒ : Bool]]]
  [(_ vs body) ≫
   [⊢ [vs ≫ vs- ⇒ : (~CList ~! ty ...)]]
   #:fail-unless (stx-andmap Constant*? #'(ty ...))
   (format "Expected list of symbolic constants, given list containing: ~a" 
           (string-join (stx-map type->str #'(ty ...)) ", "))
   [⊢ [body ≫ body- ⇐ : Bool]]
   --------
   [⊢ [_ ≫ (ro:exists vs- body-) ⇒ : Bool]]])

(define-typed-syntax verify
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:verify e-) ⇒ : CSolution]]]
  [(_ #:assume ae #:guarantee ge) ≫
   [⊢ [ae ≫ ae- ⇒ : _]]
   [⊢ [ge ≫ ge- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:verify #:assume ae- #:guarantee ge-) ⇒ : CSolution]]])

(define-typed-syntax evaluate
  [(_ v s) ≫
   [⊢ [v ≫ v- ⇒ : (~Constant* ty)]]
   [⊢ [s ≫ s- ⇐ : CSolution]]
   --------
   [⊢ [_ ≫ (ro:evaluate v- s-) ⇒ : ty]]]
  [(_ v s) ≫
   [⊢ [v ≫ v- ⇒ : ty]]
   [⊢ [s ≫ s- ⇐ : CSolution]]
   --------
   [⊢ [_ ≫ (ro:evaluate v- s-) ⇒ : #,(remove-Constant #'ty)]]])

;; TODO: enforce list of constants?
(define-typed-syntax synthesize
  [(_ #:forall ie #:guarantee ge) ≫
   [⊢ [ie ≫ ie- ⇐ : (CListof Any)]]
   [⊢ [ge ≫ ge- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:synthesize #:forall ie- #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:forall ie #:assume ae #:guarantee ge) ≫
   [⊢ [ie ≫ ie- ⇐ : (CListof Any)]]
   [⊢ [ae ≫ ae- ⇒ : _]]
   [⊢ [ge ≫ ge- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:synthesize #:forall ie- #:assume ae- #:guarantee ge-) ⇒ : CSolution]]])

(define-typed-syntax solve
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:solve e-) ⇒ : CSolution]]])

(define-typed-syntax optimize
  [(_ #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   --------
   [⊢ [_ ≫ (ro:optimize #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:minimize mine #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   [⊢ [mine ≫ mine- ⇐ : (CListof (U Num BV))]]
   --------
   [⊢ [_ ≫ (ro:optimize #:minimize mine- #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:maximize maxe #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   [⊢ [maxe ≫ maxe- ⇐ : (CListof (U Num BV))]]
   --------
   [⊢ [_ ≫ (ro:optimize #:maximize maxe- #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:minimize mine #:maximize maxe #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   [⊢ [maxe ≫ maxe- ⇐ : (CListof (U Num BV))]]
   [⊢ [mine ≫ mine- ⇐ : (CListof (U Num BV))]]
   --------
   [⊢ [_ ≫ (ro:optimize #:minimize mine- #:maximize maxe- #:guarantee ge-) ⇒ : CSolution]]]
  [(_ #:maximize maxe #:minimize mine #:guarantee ge) ≫
   [⊢ [ge ≫ ge- ⇒ : _]]
   [⊢ [maxe ≫ maxe- ⇐ : (CListof (U Num BV))]]
   [⊢ [mine ≫ mine- ⇐ : (CListof (U Num BV))]]
   --------
   [⊢ [_ ≫ (ro:optimize #:maximize maxe- #:minimize mine- #:guarantee ge-) ⇒ : CSolution]]])

;; this must be a macro in order to support Racket's overloaded set/get
;; parameter patterns
(define-typed-syntax current-solver
  [_:id ≫
   --------
   [⊢ [_ ≫ ro:current-solver ⇒ : (CParamof CSolver)]]]
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:current-solver) ⇒ : CSolver]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇐ : CSolver]]
   --------
   [⊢ [_ ≫ (ro:current-solver e-) ⇒ : CUnit]]])

;(define-rosette-primop gen:solver : CSolver)
(provide (typed-out
          [solver? : (UnliftedPredFor CSolver)]
          [solver-assert : (C→ CSolver (CListof Bool) CUnit)]
          [solver-clear : (C→ CSolver CUnit)]
          [solver-minimize : (C→ CSolver (CListof (U Int Num BV)) CUnit)]
          [solver-maximize : (C→ CSolver (CListof (U Int Num BV)) CUnit)]
          [solver-check : (C→ CSolver CSolution)]
          [solver-debug : (C→ CSolver CSolution)]
          [solver-shutdown : (C→ CSolver CUnit)]))
;; this is in rosette/solver/smt/z3 (is not in #lang rosette)
;; make this part of base typed/rosette or separate lib?
;(define-rosette-primop z3 : (C→ CSolver))

;; ---------------------------------
;; Reflecting on symbolic values

(provide (typed-out
          [term? : UnliftedPred]
          [expression? : UnliftedPred]
          [constant? : UnliftedPred]
          [type? : UnliftedPred]
          [solvable? : UnliftedPred]
          [union? : UnliftedPred]))

(define-typed-syntax union-contents
  [(_ u) ≫
   ;; TODO: can U sometimes be converted to CU?
   [⊢ [u ≫ u- ⇒ : (~and τ (~U* _ ...))]] ; input must be symbolic, and not constant
   --------
   [⊢ [_ ≫ (ro:union-contents u-) ⇒ : (CListof (CPair Bool τ))]]])

;; TODO: add match and match expanders

;; TODO: should a type-of expression have a solvable stx prop?
(provide (typed-out [type-of : (Ccase-> (C→ Any LiftedPred)
                                        (C→ Any Any LiftedPred))]
                    [any/c : (C→ Any CTrue)]))

(define-typed-syntax for/all
  ;; symbolic e
  [(_ ([x:id e]) e_body) ⇐ τ_body ≫
   [⊢ [e ≫ e- ⇒ : (~U* τ_case ...)]]
   #:with τ_x (cond [(= 1 (stx-length #'[τ_case ...]))
                     (stx-car #'[τ_case ...])]
                    [(stx-andmap concrete? #'[τ_case ...])
                     #'(CU τ_case ...)]
                    [else
                     #'(U τ_case ...)])
   [() ([x ≫ x- : τ_x]) ⊢ [e_body ≫ e_body- ⇐ : τ_body]]
   ;; Merge the τ_body with itself
   #:with τ_out (type-merge #'τ_body #'τ_body)
   ;; Check that it's a subtype of τ_body, context is expecting that
   [τ_out τ⊑ τ_body]
   --------
   [⊢ (ro:for/all ([x- e-]) e_body-)]]
  [(_ ([x:id e]) e_body) ≫
   [⊢ [e ≫ e- ⇒ : (~U* τ_case ...)]]
   #:with τ_x (cond [(= 1 (stx-length #'[τ_case ...]))
                     (stx-car #'[τ_case ...])]
                    [(stx-andmap concrete? #'[τ_case ...])
                     #'(CU τ_case ...)]
                    [else
                     #'(U τ_case ...)])
   [() ([x ≫ x- : τ_x]) ⊢ [e_body ≫ e_body- ⇒ : τ_body]]
   ;; Merge the τ_body with itself
   #:with τ_out (type-merge #'τ_body #'τ_body)
   --------
   [⊢ [_ ≫ (ro:for/all ([x- e-]) e_body-) ⇒ : τ_out]]]
  ;; known concrete e
  [(_ ([x:id e]) e_body) ⇐ τ_body ≫
   [⊢ [e ≫ e- ⇒ : τ_x]]
   #:when (concrete? #'τ_x)
   [() ([x ≫ x- : τ_x]) ⊢ [e_body ≫ e_body- ⇐ : τ_body]]
   --------
   [⊢ (ro:for/all ([x- e-]) e_body-)]]
  [(_ ([x:id e]) e_body) ≫
   [⊢ [e ≫ e- ⇒ : τ_x]]
   #:when (concrete? #'τ_x)
   [() ([x ≫ x- : τ_x]) ⊢ [e_body ≫ e_body- ⇒ : τ_body]]
   --------
   [⊢ [_ ≫ (ro:for/all ([x- e-]) e_body-) ⇒ : τ_body]]]
  ;; other, for example a symbolic constant, an Any type, or a symbolic union
  ;; type that didn't pass the first case
  [(_ ([x:id e]) e_body) ⇐ τ_body ≫
   [⊢ [e ≫ e- ⇒ : τ_x]]
   [() ([x ≫ x- : τ_x]) ⊢ [e_body ≫ e_body- ⇐ : τ_body]]
   ;; Merge the τ_body with itself
   #:with τ_out (type-merge #'τ_body #'τ_body)
   ;; Check that it's a subtype of τ_body, context is expecting that
   [τ_out τ⊑ τ_body]
   --------
   [⊢ (ro:for/all ([x- e-]) e_body-)]]
  [(_ ([x:id e]) e_body) ≫
   [⊢ [e ≫ e- ⇒ : τ_x]]
   [() ([x ≫ x- : τ_x]) ⊢ [e_body ≫ e_body- ⇒ : τ_body]]
   ;; Merge the τ_body with itself
   #:with τ_out (type-merge #'τ_body #'τ_body)
   --------
   [⊢ [_ ≫ (ro:for/all ([x- e-]) e_body-) ⇒ : τ_out]]])

(define-typed-syntax for*/all
  [(_ () e_body) ≫
   --------
   [_ ≻ e_body]]
  [(_ ([x e] [x_rst e_rst] ...) e_body) ≫
   --------
   [_ ≻ (for/all ([x e]) (for*/all ([x_rst e_rst] ...) e_body))]])

;; ------------------------------------------------------------------------

;; Errors

(provide (typed-out
          [exn:fail? (C→ Any Bool)]
          [raise-argument-error (C→ CSymbol CString Any CNothing)]))

(define-typed-syntax raise-arguments-error
  [(_ name message (~seq field v) ...) ≫
   [⊢ name ≫ name- ⇐ CSymbol]
   [⊢ message ≫ message- ⇐ CString]
   [⊢ [field ≫ field- ⇐ CString] ...]
   [⊢ [v ≫ v- ⇐ Any] ...]
   #:with [[field/v- ...] ...] #'[[field- v-] ...]
   --------
   [⊢ (ro:raise-arguments-error name- message- field/v- ... ...)
      ⇒ CNothing]])

;; ------------------------------------------------------------------------

;; Other

(provide define-syntax-rule
         define-syntax)

(define-typed-syntax begin0
  [(_ e0:expr e:expr ...) ≫
   [⊢ e0 ≫ e0- ⇒ τ]
   [⊢ [e ≫ e- ⇐ Void] ...]
   --------
   [⊢ (ro:begin0 e0- e- ...) ⇒ τ]])

;; ------------------------------------------------------------------------
;; undocumented

;; TODO: add union

;; returns all symbolic constants from e?
(define-typed-syntax symbolics
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ _]
   ---------
   [⊢ (ro:symbolics e-) ⇒ (CListof Solvable)]])

;; completes given model with given constants?
(define-typed-syntax complete
  [(_ m xs) ≫
   [⊢ m ≫ m- ⇐ CSolution]
   [⊢ xs ≫ xs- ⇒ (~CHashTable _ _)]
   -----------
   [⊢ (ro:complete m- xs-) ⇒ CSolution]])   

(define-typed-syntax (syntax e) ≫
;  [⊢ e ≫ e- ⇒ _]
  ----------
  [⊢ (syntax- e) ⇒ CStx])
