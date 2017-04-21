#lang turnstile

;; ≻ ⇒ ⇐ C→

;; TODO:
;; 2017-03-27: support defining macros in Typed Rosette?
;; 2017-03-27: support intrnl def ctxs

;; reuse unlifted forms as-is
(reuse  
 let* letrec begin #%datum ann current-join ⊔
 define-type-alias define-named-type-alias
 #:from turnstile/examples/stlc+union)
(require
 ;; manual imports
 (only-in turnstile/examples/stlc+union
          define-named-type-alias)
 ;; import typed rosette types
 "rosette/types.rkt"
 ;; import base forms
 (rename-in "rosette/base-forms.rkt" [#%app app])
 "rosette/struct-type-properties.rkt"
 (postfix-in - racket/set)
 ;; base lang
 (prefix-in ro: (combine-in rosette rosette/lib/synthax))
 (rename-in "rosette-util.rkt" [bitvector? lifted-bitvector?]))

(provide : define set! unsafe-set! λ curry apply ann begin list
         let
         (rename-out [app #%app]
                     [ro:#%module-begin #%module-begin] 
                     [λ lambda])
         prop:procedure struct-field-index
         (for-syntax get-pred expand/ro concrete?
                     syntax-case syntax/loc)
         CAny Any CNothing Nothing
         CU U (for-syntax ~CU* ~U*)
         define-syntax-rule define-syntax
         define-typed-param provide all-from-out except-in rename-out
         Constant
         C→ C→* → (for-syntax ~C→ ~C→* C→? concrete-function-type?)
         Ccase-> (for-syntax ~Ccase-> Ccase->?) ; TODO: sym case-> not supported
         CListof Listof CList CPair Pair
         (for-syntax ~CListof)
         CVectorof MVectorof IVectorof Vectorof CMVectorof CIVectorof CVector
         (for-syntax ~CMVectorof)
         CISetof CMSetof
         CParamof ; TODO: symbolic Param not supported yet
         CBoxof MBoxof IBoxof CMBoxof CIBoxof CHashTable
         (for-syntax ~CHashTable)
         CUnit Unit (for-syntax ~CUnit CUnit?)
         CNegInt NegInt
         CZero Zero
         CPosInt PosInt
         CNat Nat
         CInt Int
         CFloat Float
         CNum Num
         CFalse CTrue CBool Bool
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
(define-syntax (define-typed-param stx)
  (syntax-parse stx
    [(_ name:id ty uname:id #:cls c:id) ; TODO: tmp clause to work with untyped
     #:with cls (datum->syntax #'h (syntax->datum #'c))
     #'(define-typed-syntax name
         [_:id           ≫ --- [⊢ uname ⇒ (CParamof ty)]]
         [(_)            ≫ --- [⊢ (uname) ⇒ ty]]
         [(_ (~var e cls)) ≫ --- [⊢ (uname e) ⇒ CUnit]] ; untyped
         [(_ e) ≫
          [⊢ e ≫ e- ⇐ ty]
          --------
          [⊢ (uname e-) ⇒ CUnit]])]
    [(_ name:id ty uname:id)
     #'(define-typed-syntax name
         [_:id  ≫ --- [⊢ uname ⇒ (CParamof ty)]]
         [(_)   ≫ --- [⊢ (uname) ⇒ ty]]
         [(_ e) ≫ 
          [⊢ e ≫ e- ⇐ ty]
          --------
          [⊢ (uname e-) ⇒ CUnit]])]))
     
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
   [([x ≫ x- : (Constant ty)] ...) ⊢ [(stlc+union:begin e ...) ≫ e- ⇒ τ_out]]
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
   [([x ≫ x- : (Constant ty)] ...) ⊢ [(stlc+union:begin e ...) ≫ e- ⇒ τ_out]]
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
   [⊢ e ≫ e- ⇒ _]
   #:with pred (get-pred #'ty.norm)
   #:fail-when (and (not (syntax-e #'pred)) #'ty)
   "type does not (or cannot) have an associated predicate"
   --------
   [⊢ (ro:#%app assert-pred e- pred) ⇒ ty.norm]])

(begin-for-syntax
  (require racket/struct-info)
  (struct typed-struct (id fn)
    #:property prop:procedure (struct-field-index fn)
    #:property prop:struct-info (λ (x) (extract-struct-info
                                        (syntax-local-value
                                         (typed-struct-id x)))))
  (define (id-UPCASE stx)
    (unless (identifier? stx)
      (error 'stx-upcase "Expected identifier, given ~a" stx))
    (define chars (string->list (symbol->string (syntax->datum stx))))
    (define CHARS (map char-upcase chars))
    (datum->syntax 
     stx 
     (string->symbol (apply string CHARS)))))

;; ---------------------------------
;; Racket forms

;; TODO: get subtyping to work for struct-generated types?
;; TODO: handle mutable structs properly
(define-typed-syntax struct #:datum-literals (:)
  [(_ name:id (x:id ...+) ~! . rst) ≫
   #:fail-when #t "Missing type annotations for fields"
   --------
   [_ ≻ (ro:struct name (x ...) . rst)]]
  [(_ name:id (~optional maybe-super:id)
      ([x:id : ty:type . xrst] ...) . kws) ≫
   #:with name* (generate-temporary #'name)
   #:with Name (if (id-lower-case? #'name)
                   (id-upcase #'name)
                   (id-UPCASE #'name))
   #:with CName (format-id #'name "C~a" #'Name)
   #:with TyOut #'(Name ty ...)
   #:with CTyOut #'(CName ty ...)
   #:with (name-x ...) (stx-map (lambda (f) (format-id #'name "~a-~a" #'name f)) #'(x ...))
   #:with (name-x* ...) (stx-map (lambda (f) (format-id #'name* "~a-~a" #'name* f)) #'(x ...))
   #:with (set-x ...) (stx-map (λ (f) (format-id #'name "set-~a-~a!" #'name f)) #'(x ...))
   #:with (set-x* ...) (stx-map (λ (f) (format-id #'name* "set-~a-~a!" #'name* f)) #'(x ...))
   #:with name? (format-id #'name "~a?" #'name)
   #:with name?* (format-id #'name* "~a?" #'name*)
   #:with sups (if (attribute maybe-super) #'(maybe-super) #'())
   --------
   [≻ (ro:begin
       (ro:struct name* #,@#'sups ([x . xrst] ...) . kws)
       (define-type-constructor CName #:arity = #,(stx-length #'(x ...)))
       (define-named-type-alias (Name x ...) (U (CName x ...)))
       (define-syntax name   ; constructor
         (typed-struct
          #'name* 
          (make-variable-like-transformer
           (assign-type #'name* #'(C→ ty ... CTyOut)))))
       (define-syntax name?  ; predicate
         (make-variable-like-transformer 
          (assign-type #'name?* #'LiftedPred)))
       (define-syntax name-x ; accessors
         (make-variable-like-transformer 
          (assign-type #'name-x* #'(C→ TyOut ty)))) ...
       (define-syntax set-x ; setters
         (make-variable-like-transformer
          (assign-type #'set-x* #'(C→ TyOut ty CUnit)))) ...)]])

;; TODO: add type rules for generics
(define-typed-syntax define-generics #:datum-literals (: ->)
  [(_ name:id (f:id x:id ... -> ty-out) ... . rst) ≫
   #:with (app-f ...) (stx-map (λ (f) (format-id f "apply-~a" f)) #'(f ...))
   --------
   [≻ (ro:begin
       (ro:define-generics name (f x ...) ... . rst)
       (define-syntax app-f ; tmp workaround: each gen fn has its own apply
         (syntax-parser
           [(_ . es)
            #:with es+ (stx-map expand/df #'es)
            (assign-type #'(ro:#%app f . es+) #'ty-out)])) ...)]])

;; ---------------------------------
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

;; ---------------------------------
;; if

;; TODO: handle Cany and any
(define-typed-syntax if-concrete
  [(_ x:id e1 e2) ≫ ; x maybe symb
   [⊢ x ≫ _ ⇒ (~and ty_x (~U* ty ...))]
   [[x ≫ x- : (CU ty ...)] ⊢ e1 ≫ e1- ⇒ ty1]
   [[x ≫ y- : ty_x] ⊢ e2 ≫ e2- ⇒ ty2]
   --------
   [⊢ (ro:if (ro:term? x)
             (ro:let ([x- x]) e1-) 
             (ro:let ([y- x]) e2-)) ⇒ (U ty1 ty2)]] ; should be U?
  [(_ x:id e1 e2) ≫ ; x concrete
;   [⊢ x ≫ _ ⇒ (~and ty_x (~CU* _ ...))]
   [⊢ e2 ≫ _ ⇒ _] ; check e2 well-typed
   --------
   [≻ e1]])
(define-typed-syntax unsafe-cast-concrete
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

(define-typed-syntax if
  [(_ e_tst e1 e2) ≫
   [⊢ [e_tst ≫ e_tst- ⇒ : ty_tst]]
   #:when (or (concrete? #'ty_tst) ; either concrete
              ; or non-bool symbolic
              (not (typecheck? #'ty_tst ((current-type-eval) #'Bool))))
   [⊢ [e1 ≫ e1- ⇒ : ty1]]
   [⊢ [e2 ≫ e2- ⇒ : ty2]]
   #:when (and (concrete? #'ty1) (concrete? #'ty2))
   --------
   [⊢ [_ ≫ (ro:if e_tst- e1- e2-) ⇒ : (CU ty1 ty2)]]]
  [(_ e_tst e1 e2) ≫
   [⊢ [e_tst ≫ e_tst- ⇒ : _]]
   [⊢ [e1 ≫ e1- ⇒ : ty1]]
   [⊢ [e2 ≫ e2- ⇒ : ty2]]
   --------
   [⊢ [_ ≫ (ro:if e_tst- e1- e2-) ⇒ : (U ty1 ty2)]]])
   
(define-typed-syntax when
  [(_ x:id e ...) ≫
   [⊢ x ≫ _ ⇒ (~CU* ~CFalse ... (~and (~not ~CFalse) ty) ... ~CFalse ...)]
   [[x ≫ x- : (CU ty ...)] ⊢ (begin e ...) ≫ e- ⇒ ty-e]
   ------
   [⊢ (ro:when x (let ([x- x]) e-)) ⇒ (CU CUnit ty-e)]]
  [(_ e_tst e ...) ≫
   [⊢ e_tst ≫ e_tst- ⇒ ty_tst]
   [⊢ (begin e ...) ≫ e- ⇒ ty]
   ------
   [⊢ (ro:when e_tst- e-) ⇒ ty]])

(define-typed-syntax unless
  [(_ e_tst e) ≫
   [⊢ e_tst ≫ e_tst- ⇒ ty_tst]
   [⊢ e ≫ e- ⇒ ty]
   ------
   [⊢ (ro:unless e_tst- e-) ⇒ ty]])
   
;; ---------------------------------
;; vector

;; mutable constructor
(define-typed-syntax vector
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇒ τ] ...
   --------
   [⊢ (ro:vector e- ...) ⇒ (CMVectorof (U τ ...))]])

(provide (typed-out [vector? : LiftedPred]))

;; immutable constructor
(define-typed-syntax vector-immutable
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : τ] ...]
   --------
   [⊢ [_ ≫ (ro:vector-immutable e- ...) ⇒ : #,(if (stx-andmap concrete? #'(τ ...))
                                                  #'(CIVectorof (CU τ ...))
                                                  #'(CIVectorof (U τ ...)))]]])

;; TODO: add CList case?
;; returne mutable vector
(define-typed-syntax list->vector
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ ro:list->vector ⇒ (Ccase-> (C→ (CListof Any) (CMVectorof Any))
                                 (C→ (Listof Any) (MVectorof Any)))]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~CListof τ)]
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (CMVectorof #,(if (concrete? #'τ) #'(U τ) #'τ))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   #:with [τ* ...] (stx-map (λ (τ) (if (concrete? τ) #`(U #,τ) τ)) #'[τ ...])
   --------
   [⊢ [_ ≫ (ro:list->vector e-) ⇒ : (U (CMVectorof τ*) ...)]]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~CList τ ...)]
   --------
   [⊢ (ro:list->vector e-) ⇒ (CMVectorof (U τ ...))]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~U* (~CList τ ...) ...)]
   --------
   [⊢ (ro:list->vector e-) ⇒ (U (CMVector (U τ ...)) ...)]])
(define-typed-syntax vector->list
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~or (~CMVectorof τ) (~CIVectorof τ))]
   --------
   [⊢ (ro:vector->list e-) ⇒ (CListof τ)]])

(define-typed-syntax vector-ref
  [(_ e n) ≫
   [⊢ e ≫ e- ⇒ (~or (~CMVectorof τ) (~CIVectorof τ))]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (ro:vector-ref e- n-) ⇒ τ]]
  [(_ e n) ≫
   [⊢ e ≫ e- ⇒ (~U* (~and (~or (~CMVectorof τ) (~CIVectorof τ))) ...)]
   [⊢ n ≫ n- ⇐ Int]
   --------
   [⊢ (ro:vector-ref e- n-) ⇒ (U τ ...)]])

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
  [(_ e n v) ≫
   [⊢ e ≫ e- ⇒ (~CMVectorof τ)]
   [⊢ n ≫ n- ⇐ Int]
   [⊢ v ≫ v- ⇐ τ]
   --------
   [⊢ (ro:vector-set! e- n- v-) ⇒ CUnit]])

;; these vector fns not in rosette/safe
(define-typed-syntax make-vector
  [(_ n v) ≫
   [⊢ n ≫ n- ⇐ CNat]
   [⊢ v ≫ v- ⇒ τ]
   --------
   [⊢ (make-vector- n- v-) ⇒ #,(syntax/loc this-syntax (CMVectorof τ))]])
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

;; ---------------------------------
;; for loops (not rosette/safe)
(define-typed-syntax for/and
  [(_ ([x:id seq]) e ...) ≫ ; TODO: define pat expander for "sequence"
   [⊢ seq ≫ seq- ⇒ (~CMVectorof τ)]
   [[x ≫ x- : τ] ⊢ (begin e ...) ≫ e- ⇐ CBool]
   --------------
   [⊢ (for/and- ([x- seq-]) e-) ⇒ CBool]]
  [(_ ([x:id seq]) e ...) ≫ ; TODO: define pat expander for "sequence"
   [⊢ seq ≫ seq- ⇒ (~CMVectorof τ)]
   [[x ≫ x- : τ] ⊢ (begin e ...) ≫ e- ⇒ ty]
   --------------
   [⊢ (for/and- ([x- seq-]) e-) ⇒ (U CFalse ty)]])

(define-typed-syntax for/or
  [(_ ([x:id seq]) e ...) ≫ ; TODO: define pat expander for "sequence"
   [⊢ seq ≫ seq- ⇒ (~CMVectorof τ)]
   [[x ≫ x- : τ] ⊢ (begin e ...) ≫ e- ⇒ ty]
   --------------
   [⊢ (for/or- ([x- seq-]) e-) ⇒ #,(if (concrete? #'ty)
                                       #'(CU CFalse ty)
                                       #'(U CFalse ty))]]
  [(_ ([x:id seq] ...) e ...) ≫ ; TODO: define pat expander for "sequence"
   [⊢ seq ≫ seq- ⇐ CNat] ...
   [[x ≫ x- : CNat] ... ⊢ (begin e ...) ≫ e- ⇒ ty]
   --------------
   [⊢ (for/or- ([x- seq-] ...) e-) ⇒ #,(if (concrete? #'ty)
                                       #'(CU CFalse ty)
                                       #'(U CFalse ty))]])

(define-typed-syntax for/sum
  [(_ ([x:id seq]) e) ≫ ; TODO: define pat expander for "sequence"
   [⊢ seq ≫ seq- ⇒ (~CMVectorof _)]
   [[x ≫ x- : CInt] ⊢ e ≫ e- ⇐ CInt]
   --------------
   [⊢ (for/sum- ([x- seq-]) e-) ⇒ CInt]])

(define-typed-syntax for/list
  [(_ ([x:id seq]) e) ≫ ; TODO: define pat expander for "sequence"
   [⊢ seq ≫ seq- ⇒ (~or (~CListof ty) (~CMVectorof ty))]
   [[x ≫ x- : ty] ⊢ e ≫ e- ⇒ ty-out]
   --------------
   [⊢ (for/list- ([x- seq-]) e-) ⇒ (CListof ty-out)]])

(define-typed-syntax for
  [(_ ([x:id seq] ...) e) ≫ ; TODO: define pat expander for "sequence"
   [⊢ seq ≫ seq- ⇒ (~or (~CMVectorof τ) (~CListof τ) (~CList τ _ ...))] ...
   [[x ≫ x- : τ] ... ⊢ e ≫ e- ⇒ _]
   --------------
   [⊢ (for- ([x- seq-] ...) e-) ⇒ CUnit]]
  [(_ ([x:id seq] ... #:when tst) e) ≫
   [⊢ seq ≫ seq- ⇐ CInt] ...
   [[x ≫ x- : CInt] ... ⊢ [tst ≫ tst- ⇒ _][e ≫ e- ⇒ _]]
   --------------
   [⊢ (for- ([x- seq-] ... #:when tst-) e-) ⇒ CUnit]]
  [(_ ([x:id seq] ...) e) ≫ ; TODO: define pat expander for "sequence"
   [⊢ seq ≫ seq- ⇐ CNat] ...
   [[x ≫ x- : CNat] ... ⊢ e ≫ e- ⇒ _]
   --------------
   [⊢ (for- ([x- seq-] ...) e-) ⇒ CUnit]])

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
   [⊢ v ≫ v- ⇐ τ]
   ----------
   [⊢ (set-add!- s- v-) ⇒ CUnit]])

(define-typed-syntax set->list
  [(_ s) ≫
   [⊢ s ≫ s- ⇒ (~or (~CISetof τ) (~CMSetof τ))]
   ----------
   [⊢ (set->list- s-) ⇒ (CListof τ)]])

;; ---------------------------------
;; hash tables (not rosette/safe)

;; TODO: distinguish mutable and immutable hashes?
;; (Typed Racket does not)
(define-typed-syntax make-hash
  [(_ xs) ≫
   [⊢ xs ≫ xs- ⇒ (~CListof (~CPair tyk tyv))]
   ----------
   [⊢ (make-hash- xs-) ⇒ (CHashTable tyk tyv)]]
  [(_ xs) ≫
   [⊢ xs ≫ xs- ⇒ (~CList (~CPair tyk0 tyv0) (~CPair tyk tyv) ...)]
   #:when (and (same-types? #'(tyk0 tyk ...))
               (same-types? #'(tyv0 tyv ...)))
   ----------
   [⊢ (make-hash- xs-) ⇒ (CHashTable tyk0 tyv0)]]
  [(_ _) ≫
   ----
   [#:error "can't infer types of elements; add annotations"]])

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
(define-typed-syntax hash-set
  [(_ e k v) ≫
   [⊢ e ≫ e- ⇒ (~and ty-out (~CHashTable τk τv))]
   [⊢ k ≫ k- ⇐ τk]
   [⊢ v ≫ v- ⇐ τv]
   --------
   [⊢ (hash-set- e- k- v-) ⇒ ty-out]])
(define-typed-syntax hash-clear!
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~CHashTable _ _)]
   --------
   [⊢ (hash-clear!- e-) ⇒ CUnit]])
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
(define-typed-syntax hash-ref
  [(_ e k) ≫
   [⊢ e ≫ e- ⇒ (~CHashTable τk τv)]
   [⊢ k ≫ k- ⇐ τk]
   --------
   [⊢ (hash-ref- e- k-) ⇒ τv]]
  [(_ e k v_def) ≫
   [⊢ e ≫ e- ⇒ (~CHashTable τk τv)]
   [⊢ k ≫ k- ⇐ τk]
   [⊢ v_def ≫ v_def- ⇒ ty_def]
   --------
   [⊢ (hash-ref- e- k- v_def-) ⇒ (CU ty_def τv)]])
(define-typed-syntax hash-values
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~CHashTable _ τ)]
   --------
   [⊢ (hash-values- e-) ⇒ (CListof τ)]])

;; ---------------------------------
;; lists

(provide (typed-out [null? : (Ccase-> (C→ (CListof Any) CBool)
                                      (C→ (Listof Any) Bool))]
                    [empty? : (Ccase-> (C→ (CListof Any) CBool)
                                       (C→ (Listof Any) Bool))]
                    [list? : LiftedPred]))

(define-typed-syntax null
  [(_ {τ}) ≫
   --------
   [⊢ ro:null ⇒ (CListof τ)]])

(define-typed-syntax list
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : τ] ...]
   --------
   [⊢ [_ ≫ (ro:list e- ...) ⇒ : (CList τ ...)]]])

(define-typed-syntax cons
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:cons ⇒ : (Ccase-> 
                        (C→ Any Any (CPair Any Any))
                        (C→ Any (CListof Any) (CListof Any))
                        (C→ Any (Listof Any) (Listof Any)))]]]
  [(_ e1 e2) ≫
   [⊢ [e2 ≫ e2- ⇒ : (~CListof τ1)]]
   [⊢ [e1 ≫ e1- ⇒ : τ2]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) 
           ⇒ : #,(if (and (concrete? #'τ1) (concrete? #'τ2))
                     #'(CListof (CU τ1 τ2))
                     #'(CListof (U τ1 τ2)))]]]
  [(_ e1 e2) ≫
   [⊢ [e2 ≫ e2- ⇒ : (~U* (~CListof τ) ...)]]
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (U (CListof (U τ1 τ)) ...)]]]
  [(_ e1 e2) ≫
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : (~CList τ ...)]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (CList τ1 τ ...)]]]
  [(_ e1 e2) ≫
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : (~U* (~CList τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (U (CList τ1 τ ...) ...)]]]
  [(_ e1 e2) ≫
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : τ2]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (CPair τ1 τ2)]]])

;; car and cdr additionally support pairs
(define-typed-syntax car
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:car ⇒ : (Ccase-> (C→ (Pair Any Any) Any)
                               (C→ (Listof Any) Any))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : (U τ ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : τ1]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : (U τ1 ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CPair τ _)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CPair τ _) ...)]]
   --------
   [⊢ [_ ≫ (ro:car e-) ⇒ : (U τ ...)]]])

(define-typed-syntax cdr
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:cdr ⇒ : (Ccase-> (C→ (CListof Any) (CListof Any))
                                (C→ (Listof Any) (Listof Any)))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (CListof τ)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (CList τ ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (U (CList τ ...) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CPair _ τ)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CPair _ τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:cdr e-) ⇒ : (U τ ...)]]])


(define-typed-syntax first
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:first ⇒ : (C→ (Listof Any) Any)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:first e-) ⇒ : τ]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:first e-) ⇒ : (U τ ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:first e-) ⇒ : τ1]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:first e-) ⇒ : (U τ1 ...)]]])

(define-typed-syntax rest
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:rest ⇒ : (Ccase-> (C→ (CListof Any) (CListof Any))
                                (C→ (Listof Any) (Listof Any)))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:rest e-) ⇒ : (CListof τ)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:rest e-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:rest e-) ⇒ : (CList τ ...)]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:rest e-) ⇒ : (U (CList τ ...) ...)]]])

(define-typed-syntax second
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ ro:second ⇒ (C→ (Listof Any) Any)]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~CListof τ)]
   --------
   [⊢ (ro:second e-) ⇒ τ]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~U* (~CListof τ) ...)]
   --------
   [⊢ (ro:second e-) ⇒ (U τ ...)]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~CList τ1 τ2 τ ...)]
   --------
   [⊢ (ro:second e-) ⇒  τ2]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~U* (~CList τ1 τ2 τ ...) ...)]
   --------
   [⊢ (ro:second e-) ⇒  (U τ2 ...)]])

(define-typed-syntax list-ref
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ ro:list-ref ⇒ (C→ (Listof Any) CNat Any)]]
  [(_ e i) ≫
   [⊢ e ≫ e- ⇒ (~CListof τ)]
   [⊢ i ≫ i- ⇐ CNat]
   --------
   [⊢ (ro:list-ref e- i-) ⇒ τ]]
  [(_ ei) ≫
   [⊢ e ≫ e- ⇒ (~U* (~CListof τ) ...)]
   [⊢ i ≫ i- ⇐ CNat]
   --------
   [⊢ (ro:list-ref e- i-) ⇒ (U τ ...)]]
  [(_ e i) ≫
   [⊢ e ≫ e- ⇒ (~CList τ1 τ2 τ ...)]
   [⊢ i ≫ i- ⇐ CNat]
   --------
   [⊢ (ro:list-ref e- i-) ⇒  τ2]]
  [(_ e i) ≫
   [⊢ e ≫ e- ⇒ (~U* (~CList τ1 τ2 τ ...) ...)]
   [⊢ i ≫ i- ⇐ CNat]
   --------
   [⊢ (ro:list-ref e- i-) ⇒  (U τ2 ...)]])

;; TODO: add other remove cases
(define-typed-syntax remove
  [(_ v lst) ≫
   [⊢ lst ≫ lst- ⇒ (~and ty-out (~CListof τ))]
   [⊢ v ≫ v- ⇐ τ] ; is this actually a type error?
   --------
   [⊢ (ro:remove v- lst-) ⇒ ty-out]]
  [(_ v lst) ≫
   [⊢ lst ≫ lst- ⇒ (~CList τ ...)]
   [⊢ v ≫ v- ⇒ τv]
;   #:when (typecheck? #'τv #'(U τ ...))
   ;; TODO: this is wrong bc it will remove the first type in (τ ...) that
   ;; matches τv but that might not be the removed element
   ;; - best solution is to return clistof union type
;;   #:with (τo ...) (stx-remove #'τv #'(τ ...) typecheck?)
   --------
   [⊢ (ro:remove v- lst-) ⇒ (CListof (CU τ ...))]])

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

(define-typed-syntax length
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:length ⇒ : (Ccase-> (C→ (CListof Any) CNat)
                                (C→ (Listof Any) Nat))]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇐ : (CListof Any)]]
   --------
   [⊢ [_ ≫ (ro:length e-) ⇒ : CNat]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof _) ...)]]
   --------
   [⊢ [_ ≫ (ro:length e-) ⇒ : Nat]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~CList _ ...)]]
   --------
   [⊢ [_ ≫ (ro:length e-) ⇒ : CNat]]]
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList _ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:length e-) ⇒ : Nat]]])

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

(define-typed-syntax map
  [(_ f lst ...) ≫
   [⊢ f ≫ f- ⇒ (~C→ ~! ty1 ... ty2)]
   [⊢ lst ≫ lst- ⇐ (CListof ty1)] ...
   --------
   [⊢ (ro:map f- lst- ...) ⇒ (CListof ty2)]]
  [(_ f lst ...) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof ty1)] ...
   [⊢ f ≫ f- ⇒ (~Ccase-> ~! ty-fns ...)] ; find first match
   #:with (~C→ _ ty2)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ t1 ... _)
                                #:when (typechecks? #'(ty1 ...) #'(t1 ...))
                                #t]
                               [_ #f]))
            (displayln (syntax->datum ty-fn))
            ty-fn)
   --------
   [⊢ (ro:map f- lst- ...) ⇒ (CListof ty2)]]
  [(_ f lst ...) ≫
   [⊢ lst ≫ lst- ⇒ (~U* (~CListof ty1))] ...
   [⊢ f ≫ f- ⇒ (~Ccase-> ~! ty-fns ...)] ; find first match
   #:with (~C→ _ ty2)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ t1 ... _)
                                #:when (typechecks? #'(ty1 ...) #'(t1 ...))
                                #t]
                               [_ #f]))
            ty-fn)
   --------
   [⊢ (ro:map f- lst- ...) ⇒ (CListof ty2)]])

(define-typed-syntax for-each
  [(_ f lst ...) ≫
   [⊢ f ≫ f- ⇒ (~C→ ~! ty1 ... _)]
   [⊢ lst ≫ lst- ⇐ (CListof ty1)] ...
   --------
   [⊢ (ro:for-each f- lst- ...) ⇒ CUnit]]
  [(_ f lst ...) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof ty1)] ...
   [⊢ f ≫ f- ⇒ (~Ccase-> ~! ty-fns ...)] ; find first match
   #:with (~C→ _ _)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ t1 ... _)
                                #:when (typechecks? #'(ty1 ...) #'(t1 ...))
                                #t]
                               [_ #f]))
            (displayln (syntax->datum ty-fn))
            ty-fn)
   --------
   [⊢ (ro:for-each f- lst- ...) ⇒ CUnit]]
  [(_ f lst ...) ≫
   [⊢ lst ≫ lst- ⇒ (~U* (~CListof ty1))] ...
   [⊢ f ≫ f- ⇒ (~Ccase-> ~! ty-fns ...)] ; find first match
   #:with (~C→ _ _)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ t1 ... _)
                                #:when (typechecks? #'(ty1 ...) #'(t1 ...))
                                #t]
                               [_ #f]))
            ty-fn)
   --------
   [⊢ (ro:for-each f- lst- ...) ⇒ CUnit]])

(define-typed-syntax filter
  [(_ f lst) ≫
   [⊢ f ≫ f- ⇒ (~C→ ~! ty1 Bool)]
   [⊢ lst ≫ lst- ⇐ (CListof ty1)]
   --------
   [⊢ (ro:filter f- lst-) ⇒ (CListof ty1)]]
  #;[(_ f lst) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof ty1)]
   [⊢ f ≫ f- ⇒ (~Ccase-> ~! ty-fns ...)] ; find first match
   #:with (~C→ _ ty2)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ t1 _) #:when (typecheck? #'ty1 #'t1) #t]
                               [_ #f]))
            (displayln (syntax->datum ty-fn))
            ty-fn)
   --------
   [⊢ (ro:map f- lst-) ⇒ (CListof ty2)]]
  #;[(_ f lst) ≫
   [⊢ lst ≫ lst- ⇒ (~U* (~CListof ty1))]
   [⊢ f ≫ f- ⇒ (~Ccase-> ~! ty-fns ...)] ; find first match
   #:with (~C→ _ ty2)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ t1 _) #:when (typecheck? #'ty1 #'t1) #t]
                               [_ #f]))
            ty-fn)
   --------
   [⊢ (ro:map f- lst-) ⇒ (CListof ty2)]])

(define-typed-syntax filter-not
  [(_ f lst) ≫
   [⊢ f ≫ f- ⇒ (~or (~C→ _ Bool)
                     (~Ccase-> (~and _ (~not (~C→ _ Bool))) ...
                               (~C→ _ Bool)
                               _ ...))]
   [⊢ lst ≫ lst- ⇒ (~CListof ty)]
   --------
   [⊢ (ro:filter-not f- lst-) ⇒ (CListof ty)]])

;; TODO: finish andmap and ormap
(define-typed-syntax andmap
  [(_ f lst) ≫
   [⊢ f ≫ f- ⇒ (~C→ ~! ty ty-bool)]
   [⊢ lst ≫ lst- ⇒ (~CListof _)]
   --------
   [⊢ (ro:andmap f- lst-) ⇒ Bool]])

(define-typed-syntax ormap
  [(_ f lst) ≫
   [⊢ f ≫ f- ⇒ (~C→ ~! ty ty-bool)]
   [⊢ lst ≫ lst- ⇒ (~CListof _)]
   --------
   [⊢ (ro:ormap f- lst-) ⇒ Bool]])

(define-typed-syntax foldl
  [(_ f base lst) ≫
   [⊢ f ≫ f- ⇒ (~C→ ~! ty ty-res-in ty-res-out)]
   #:when (typecheck? #'ty-res-in #'ty-res-out)
   [⊢ base ≫ base- ⇐ ty-res-in]
   [⊢ lst ≫ lst- ⇐ (CListof ty)]
   --------
   [⊢ (ro:foldl f- base- lst-) ⇒ ty-res-out]])

(define-typed-syntax remove-duplicates
  [(_ lst) ≫
   [⊢ lst ≫ lst- (⇐ (Listof Any)) (⇒ ty-out)]
   --------
   [⊢ (ro:remove-duplicates lst-) ⇒ ty-out]])

(define-typed-syntax sort
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:sort ⇒ : (Ccase-> (C→ (CListof Any) LiftedPred2 (CListof Any))
                                (C→ (Listof Any) LiftedPred2 (Listof Any)))]]]
  [(_ e cmp) ≫
   [⊢ [e ≫ e- ⇒ : (~CListof τ)]]
   [⊢ [cmp ≫ cmp- ⇐ : (C→ τ τ Bool)]]
   --------
   [⊢ [_ ≫ (ro:sort e- cmp-) ⇒ : (CListof τ)]]]
  [(_ e cmp) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CListof τ) ...)]]
   [⊢ [cmp ≫ cmp- ⇐ : (C→ (U τ ...) (U τ ...) Bool)]]
   --------
   [⊢ [_ ≫ (ro:sort e- cmp-) ⇒ : (U (CListof τ) ...)]]]
  [(_ e cmp) ≫
   [⊢ [e ≫ e- ⇒ : (~CList . τs)]]
   [⊢ [cmp ≫ cmp- ⇐ : (C→ (U . τs) (U . τs) Bool)]]
   --------
   [⊢ [_ ≫ (ro:sort e- cmp-) ⇒ : (CListof (U . τs))]]]
  [(_ e cmp) ≫
   [⊢ [e ≫ e- ⇒ : (~U* (~CList τ ...) ...)]]
   [⊢ [cmp ≫ cmp- ⇐ : (C→ (U τ ... ...) (U τ ... ...) Bool)]]
   --------
   [⊢ [_ ≫ (ro:sort e- cmp-) ⇒ : (U (CList (U τ ...)) ...)]]])

;; list forms and fns not in rosette/safe
(define-typed-syntax build-list
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ ro:build-list ⇒ (C→ CNat (C→ CNat Any) (CListof Any))]]
  [(_ n f) ≫
   [⊢ n ≫ n- ⇐ CInt]
   [⊢ f ≫ f- ⇒ (~C→ ty1 ty2)]
   #:fail-unless (typecheck? #'ty1 ((current-type-eval) #'CInt))
                 "expected function that consumes concrete Int"
   --------
   [⊢ (ro:build-list n- f-) ⇒ (CListof ty2)]])

(provide (typed-out [range : (Ccase-> (C→ CNat (CListof CNat)))]))

;; ---------------------------------
;; IO and other built-in ops

(provide (typed-out [void : (C→ CUnit)]
                    [printf : (Ccase-> (C→ CString CUnit)
                                       (C→ CString Any CUnit)
                                       (C→ CString Any Any CUnit))]
                    [display : (C→ Any CUnit)]
                    [displayln : (C→ Any CUnit)]
                    [with-output-to-string : (C→ (C→ Any) CString)]
                    [string-contains? : (C→ CString CString CBool)]
                    [pretty-print : (C→ Any CUnit)]
                    [error : (Ccase-> (C→ (CU CString CSymbol) CNothing)
                                      (C→ CSymbol CString CNothing))]

                    [string-length : (C→ CString CNat)]
                    [string-append : (C→ CString CString CString)]

                    [equal? : LiftedPred2]
                    [eq? : LiftedPred2]
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
                    
                    [not : LiftedPred]
                    [xor : (Ccase-> (C→ CAny CAny CAny)
                                    (C→ Any Any Any))]
                    [false? : LiftedPred]
                    [true : CTrue]
                    [false : CFalse]
                    [real->integer : (C→ Num Int)]
                    [string? : UnliftedPred]
                    [number? : LiftedPred]
                    [positive? : LiftedNumPred]
                    [negative? : LiftedNumPred]
                    [zero? : LiftedNumPred]
                    [even? : LiftedIntPred]
                    [odd? : LiftedIntPred]
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
                    ;; unlifted, not in rosette/safe
                    [random : (Ccase-> (C→ CPosInt CNat)
                                       (C→ CNat CNat))]
                    
                    ;; rosette-specific
                    [pc : (C→ Bool)]
                    [asserts : (C→ CAsserts)]
                    [clear-asserts! : (C→ CUnit)]))

;; ---------------------------------
;; more built-in ops

;(define-rosette-primop boolean? : (C→ Any Bool))
(define-typed-syntax boolean?
  [_:id ≫
   --------
   [⊢ (mark-solvablem
       (add-typeform
        ro:boolean?
        Bool)) ⇒ LiftedPred]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ ty]
   --------
   [⊢ (ro:boolean? e-) ⇒ #,(if (concrete? #'ty) #'CBool #'Bool)]])

;(define-rosette-primop integer? : (C→ Any Bool))
(define-typed-syntax integer?
  [_:id ≫
   --------
   [⊢ (mark-solvablem
       (add-typeform
        ro:integer?
        Int)) ⇒ LiftedPred]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ ty]
   --------
   [⊢ (ro:integer? e-) ⇒ #,(if (concrete? #'ty) #'CBool #'Bool)]])

;(define-rosette-primop real? : (C→ Any Bool))
(define-typed-syntax real?
  [_:id ≫
   --------
   [⊢ (mark-solvablem
       (add-typeform
        ro:real?
        Num)) ⇒ LiftedPred]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ ty]
   --------
   [⊢ (ro:real? e-) ⇒ #,(if (concrete? #'ty) #'CBool #'Bool)]])

(define-typed-syntax time
  [(_ e) ≫
   [⊢ [e ≫ e- ⇒ : ty]]
   --------
   [⊢ [_ ≫ (ro:time e-) ⇒ : ty]]])

;; ---------------------------------
;; mutable boxes

(define-typed-syntax box
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ τ]
   --------
   [⊢ [_ ≫ (ro:box e-) ⇒ : (CMBoxof #,(if (concrete? #'τ) #'(U τ) #'τ))]]])

(define-typed-syntax box-immutable
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ τ]
   --------
   [⊢ (ro:box-immutable e-) ⇒ (CIBoxof τ)]])

(define-typed-syntax unbox
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~or (~CMBoxof τ) (~CIBoxof τ))]
   --------
   [⊢ (ro:unbox e-) ⇒ τ]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ (~U* (~and (~or (~CMBoxof τ) (~CIBoxof τ))) ...)]
   --------
   [⊢ (ro:unbox e-) ⇒ (U τ ...)]])

(define-typed-syntax set-box!
  [(_ e v) ≫
   [⊢ e ≫ e- ⇒ (~CMBoxof τ)]
   [⊢ v ≫ v- ⇐ τ]
   --------
   [⊢ (ro:set-box! e- v-) ⇒ CUnit]])

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
                    [bv? : LiftedPred]
                    
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
       (add-typeform
        (ro:bitvector n-)
        BV)) ⇒ CBVPred]])

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
        (add-typeform
         (ro:~> pred?- ... out-)
         (→ ty ... ty-out)))) ⇒ LiftedPred]])

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
           (Ccase-> (C→ Bool)
                    (C→ Bool Bool)
                    (C→ Bool Bool Bool))]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇐ : Bool] ...]
   --------
   [⊢ [_ ≫ (ro:&& e- ...) ⇒ : Bool]]])
(define-typed-syntax ||
  [_:id ≫
   --------
   [⊢ [_ ≫ ro:|| ⇒ :
           (Ccase-> (C→ Bool)
                    (C→ Bool Bool)
                    (C→ Bool Bool Bool))]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇐ : Bool] ...]
   --------
   [⊢ [_ ≫ (ro:|| e- ...) ⇒ : Bool]]])

(define-typed-syntax and
  [(_) ≫
   --------
   [⊢ (ro:and) ⇒ CTrue]]
  [(_ e ... elast) ≫
   [⊢ e ≫ e- ⇒ ty] ...
   #:when (stx-andmap concrete? #'(ty ...))
   [⊢ elast ≫ elast- ⇒ ty-last]
   #:when (concrete? #'ty-last)
   --------
   [⊢ (ro:and e- ... elast-) ⇒ (CU CFalse ty-last)]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Bool] ...
   --------
   [⊢ (ro:and e- ...) ⇒ Bool]]
  [(_ e ... elast) ≫
   [⊢ e ≫ e- ⇒ ty] ...
   [⊢ elast ≫ elast- ⇒ ty-last]
   --------
   [⊢ (ro:and e- ... elast-) ⇒ (U CFalse ty-last)]])
(define-typed-syntax or
  [(_) ≫
   --------
   [⊢ (ro:or) ⇒ CFalse]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ CBool] ...
   --------
   [⊢ (ro:or e- ...) ⇒ CBool]]
  [(_ e ...) ≫
   [⊢ e ≫ e- ⇐ Bool] ...
   --------
   [⊢ (ro:or e- ...) ⇒ Bool]]
  [(_ e ...) ≫ ; some symbolic vals
   [⊢ e ≫ e- ⇒ ty] ...
   #:with ((~or ~CFalse non-f) ...) #'(ty ...)
   #:with ((~and (~not (~U* . _)) _) ... (~U* . _) . _) #'(non-f ...)
   --------
   [⊢ (ro:or e- ...) ⇒ (U non-f ...)]]
  [(_ e ...) ≫ ; all concrete
   [⊢ e ≫ e- ⇒ ty] ...
   #:with ((~or ~CFalse non-f) ...) #'(ty ...)
   --------
   [⊢ (ro:or e- ...) ⇒ (CU non-f ...)]])
#;(define-typed-syntax not
  [(_ e) ≫
   [⊢ e ≫ e- ⇐ CBool]
   --------
   [⊢ (ro:not e-) ⇒ CBool]]
  [(_ e) ≫
   [⊢ e ≫ e- ⇐ Bool]
   --------
   [⊢ (ro:not e-) ⇒ Bool]])
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
                    [solution? : UnliftedPred]
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
          [solver? : UnliftedPred]
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
  [(_ ([x:id e]) e_body) ≫
   ;; TODO: this is unsound!
   ;; See issue #12
   [⊢ [e ≫ e- ⇒ : (~U* τ_x)]]
   [() ([x ≫ x- : τ_x]) ⊢ [e_body ≫ e_body- ⇒ : τ_body]]
   --------
   [⊢ [_ ≫ (ro:for/all ([x- e-]) e_body-) ⇒ : (U τ_body)]]]
  ;; known concrete e
  [(_ ([x:id e]) e_body) ≫
   [⊢ [e ≫ e- ⇒ : τ_x]]
   #:when (concrete? #'τ_x)
   [() ([x ≫ x- : τ_x]) ⊢ [e_body ≫ e_body- ⇒ : τ_body]]
   --------
   [⊢ [_ ≫ (ro:for/all ([x- e-]) e_body-) ⇒ : τ_body]]]
  ;; other, for example a symbolic constant, an Any type, or a symbolic union
  ;; type that didn't pass the first case
  [(_ ([x:id e]) e_body) ≫
   [⊢ e ≫ e- ⇒ τ_x]
   [[x ≫ x- : τ_x] ⊢ e_body ≫ e_body- ⇒ τ_body]
   --------
   [⊢ (ro:for/all ([x- e-]) e_body-) ⇒ τ_body]]) ; why is out ty the same?

(define-typed-syntax for*/all
  [(_ () e_body) ≫
   --------
   [_ ≻ e_body]]
  [(_ ([x e] [x_rst e_rst] ...) e_body) ≫
   --------
   [_ ≻ (for/all ([x e]) (for*/all ([x_rst e_rst] ...) e_body))]])

;; undocumented ----------------------------------------

;; TODO: add union

;; returns all symbolic constants from e?
(define-typed-syntax symbolics
  [(_ e) ≫
   [⊢ e ≫ e- ⇒ _]
   ---------
   [⊢ (ro:symbolics e-) ⇒ (CListof Any)]])

;; completes given model with given constants?
(define-typed-syntax complete
  [(_ m xs) ≫
   [⊢ m ≫ m- ⇐ CSolution]
   [⊢ xs ≫ xs- ⇒ (~CHashTable _ _)]
   -----------
   [⊢ (ro:complete m- xs-) ⇒ CSolution]])   

;; ---------------------------------
;; require and provide
(define-typed-syntax require-typed-in
  [(_ m [x:id (~datum :) ty] ...) ≫
   #:with (x- ...) (generate-temporaries #'(x ...))
   ---------
   [≻ (ro:begin
       (require- (only-in- m [x x-] ...))
       (define-syntax- x (make-variable-like-transformer (assign-type #'x- #'ty))) ...)]])

;; eval ------------------------------
(provide (typed-out ;[[eval-syntax- : (C→ Any Any)] eval-syntax]
                    ;[[eval- : (C→ Any Any)] eval]
                    #;[[datum->syntax : (C→ Any Any Any)] datum->syntax]))

(define-typed-syntax (eval e) ≫
;  [⊢ e ≫ e- ⇒ _]
  ----------
  [⊢ (eval- e) ⇒ Any])
(define-typed-syntax (eval-syntax e) ≫
;  [⊢ e ≫ e- ⇒ _]
  ----------
  [⊢ (eval-syntax- e) ⇒ Any])
(define-typed-syntax (syntax e) ≫
;  [⊢ e ≫ e- ⇒ _]
  ----------
  [⊢ (syntax- e) ⇒ CStx])

;; (define-typed-syntax (eval-syntax e) ≫
;;   [⊢ e ≫ e- ⇒ _]
;;   ----------
;;   [⊢ (eval-syntax- e-) ⇒ Any])

(define-typed-syntax (datum->syntax ctx e) ≫
  ---------
  [⊢ (datum->syntax- ctx e) ⇒ CStx])

;; oo -----------------------------------------
;; bypass typechecker for now, since
;; these are only used internally (eg, not by programmer)

(require (postfix-in - racket/class))

(define-typed-syntax (send . args) ≫
  ---------
  [⊢ (send- . args) ⇒ Any])

(define-typed-syntax (new . args) ≫
  ---------
  [⊢ (new- . args) ⇒ Any])

;; untyped passthroughs --------------------------------------------------

(define-typed-syntax (untyped-let () . args) ≫
  ---------
  [⊢ (begin- . args) ⇒ Any])

(define-typed-syntax (untyped-begin . args) ≫
  ---------
  [⊢ (begin- . args) ⇒ Any])

