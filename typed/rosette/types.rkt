#lang turnstile

(provide CAnyDeep CAny Any
         CNothing Nothing
         Term
         CU U
         Constant Solvable
         (for-syntax Any?
                     ~Term*
                     ~CU* ~U* CU*? U*?
                     ~Constant* Constant*? remove-Constant
                     concrete?
                     concrete/shallow-recur?)
         ;; Struct types
         Struct
         (for-syntax typed-struct-id
                     typed-struct-info
                     typed-struct-info-predicate
                     typed-struct-info-accessors
                     typed-struct-info-field-types)
         ;; Function types
         C→ C→* C→/conc C→** Ccase-> → →/conc
         (for-syntax concrete-function-type?
                     ~C→ ~C→/conc ~C→* ~C→** ~Ccase->
                     C→? Ccase->?)
         ;; Propositions for Occurrence typing
         @ !@
         Prop
         Prop/Top
         Prop/Bot
         Prop/ObjType
         Prop/ObjNotType
         Prop/Or
         Prop/And
         with-occurrence-prop
         (for-syntax prop-instantiate get-arg-obj
                     ~Prop/IndexType)
         ;; Parameters
         CParamof ; TODO: symbolic Param not supported yet
         ;; List types
         CListof CList CPair
         Listof Pair
         (for-syntax ~CListof ~CList ~CPair)
         ;; Other container types
         CHashTable
         (rename-out [CHashTable CHashof])
         CSequenceof
         CISetof CMSetof
         CBoxof CMBoxof CIBoxof MBoxof IBoxof
         CVectorof CMVectorof CIVectorof CVector
         Vectorof MVectorof IVectorof
         (for-syntax ~CHashTable
                     (rename-out [~CHashTable ~CHashof])
                     ~CSequenceof
                     ~CMSetof ~CISetof
                     ~CMBoxof ~CIBoxof
                     ~CMVectorof ~CIVectorof)
         ;; BV types
         CBV BV
         CBVPred BVPred
         ;; Structure Type Properties
         CStructTypeProp
         (for-syntax ~CStructTypeProp)
         ;; Other base types
         CUnit Unit
         (rename-out [CUnit CVoid] [Unit Void])
         CZero Zero
         CPosInt PosInt
         CNegInt NegInt
         CNat Nat
         CInt Int
         CFloat Float
         CNum Num
         CFalse CTrue CBool False True Bool
         CString String
         CStx
         CSymbol
         CAsserts
         COutputPort
         CSolution CSolver CPict CRegexp CSymbol
         LiftedPred LiftedPred2
         LiftedPredDeep LiftedPredDeep2
         LiftedNumPred LiftedIntPred UnliftedPred
         LiftedPredFor UnliftedPredFor
         (for-syntax ~CUnit CUnit?
                     (rename-out [~CUnit ~CVoid] [CUnit? CVoid?])
                     ~CString CString?
                     ~CTrue ~CFalse)
         ;; The relationship between types and
         ;; rosette's run-time type predicates
         add-predm
         add-typeform
         mark-solvablem
         mark-functionm
         (for-syntax current-sym-path? current-sym-scope no-mut-msg conc-fn-msg
                     no-mutate? no-mutate/ty? not-current-sym-scope?
                     mk-path-sym mk-path-conc
                     save-sym-path-info restore-sym-path-info 
                     get-pred
                     type-merge
                     type-merge*
                     typeCNothing
                     typeCFalse
                     typeCTrue
                     occurrence-env))

(require (only-in turnstile/examples/stlc+union
           define-named-type-alias prune+sort current-sub?)
         (prefix-in C
           (only-in turnstile/examples/stlc+union+case
             PosInt Zero NegInt Float True False
             String String?
             Unit Unit?))
         (only-in turnstile/examples/stlc+union+case
           [U CU*] [~U* ~CU*] [U*? CU*?]
           [case-> Ccase->*] [~case-> ~Ccase->] [case->? Ccase->?]
           [→ C→/normal] [~→ ~C→/normal] [→? C→/normal?]
           [~PosInt ~CPosInt] [~Zero ~CZero] [~NegInt ~CNegInt]
           [~True ~CTrue] [~False ~CFalse]
           [~String ~CString]
           [~Unit ~CUnit])
         (only-in turnstile/examples/stlc+cons
           [List CListof] [~List ~CListof])
         (prefix-in ro: rosette)
         (prefix-in ro: rosette/lib/synthax)
         (rename-in "../rosette-util.rkt" [bitvector? lifted-bitvector?])
         "concrete-predicate.rkt")

(require (for-syntax racket/struct-info
                     syntax/id-table
                     syntax/parse/class/local-value
                     syntax/parse/class/struct-id))

;; ---------------------------------
;; Concrete and Symbolic union types

;; internal symbolic union constructor
(define-type-constructor U* #:arity >= 0)

;; internal symbolic term constructor
(define-type-constructor Term* #:arity = 1)

;; internal symbolic constant constructor
(define-type-constructor Constant* #:arity = 1)

(begin-for-syntax
  (define (concrete? t)
    (not (or (Any? t) (U*? t) (Term*? t) (Constant*? t))))
  (define (concrete/recur? t)
    (and (concrete? t)
         (syntax-parse t
           [(~Any _ . tys)
            (stx-andmap concrete/recur? #'tys)]
           [_ #t])))

  ;; Solvable types are types that can appear within (Term X)
  (define (type-solvable? τ)
    (or (Term*? τ)
        (concrete-type-solvable? τ)))

  ;; Single-Shape types are types that don't create symbolic unions when merged
  (define (type-single-shape? τ)
    (and (type-single-shape τ) #true))
  (define (type-single-shape τ)
    (syntax-parse τ
      [(~Term* τ) (concrete-type-single-shape #'τ)]
      [_ (concrete-type-single-shape τ)]))

  ;; indicates whether the path is currently symbolic
  ;; needed for soundness,
  ;;   eg reject mutation of concrete-typed vars in symbolic path
  (define current-sym-path? (make-parameter #f))
  (define (no-mutate/ty? ty)
    (and (current-sym-path?) (concrete? ty)))
  (define (no-mutate? e)
    (and (no-mutate/ty? (typeof e)) (not-current-sym-scope? e)))
  (define (no-mut-msg wh . args)
    (apply
     format
     (string-append "Cannot mutate concrete " wh " when in a symbolic path")
     args))
  (define (conc-fn-msg)
    "Cannot apply function with C→/conc type when in a symbolic path")

  ;; each new sym path is associated with a "sym scope"
  ;; - variables may be introduced and mutated within the same sym scope
  ;; - define an initial symscope to avoid confusion when stx doesnt have prop
  (define current-sym-scope (make-parameter (gensym)))
  (define (mk-path-sym)
    (current-sym-scope (gensym))
    (current-sym-path? #t))
  (define (mk-path-conc)
    (current-sym-path? #f))
  (define (not-current-sym-scope? x)
    (not (equal? (syntax-property x 'sym-scope) (current-sym-scope))))

  ;; used to save previous values of current-sym-path?/scope
  (define old-sym-path? (make-parameter (current-sym-path?)))
  (define old-sym-scope (make-parameter (current-sym-scope)))
  (define (save-sym-path-info)
    (old-sym-path? (current-sym-path?))
    (old-sym-scope (current-sym-scope)))
  (define (restore-sym-path-info)
    (current-sym-path? (old-sym-path?))
    (current-sym-scope (old-sym-scope)))
  )

;; TODO: update orig to use reduced type
(define-syntax (CU stx)
  (syntax-parse stx
    [(_ . tys)
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap concrete? #'tys+)
                   "CU requires concrete types"
     (syntax/loc this-syntax (CU* . tys+))]))

;; user-facing symbolic U constructor: flattens and prunes
(define-syntax (U stx)
  (syntax-parse stx
    [(_ . tys)
     ;; canonicalize by expanding to U*, with only (sorted and pruned) leaf tys
     #:with ((~or (~U* ty1- ...) (~CU* ty2- ...) ty3-) ...) (stx-map (current-type-eval) #'tys)
     #:with tys- (prune+sort #'(ty1- ... ... ty2- ... ... ty3- ...))
     (syntax/loc this-syntax (U* . tys-))]))

;; user-facing symbolic Term constructor: check solvable
(define-syntax-parser Term
  [(_ τ:type)
   #:fail-when (and (not (type-solvable? #'τ.norm)) #'τ)
   (format "expected a solvable type, given ~a" (type->str #'τ.norm))
   (if (Term*? #'τ.norm)
       #'τ.norm
       (syntax/loc this-syntax (Term* τ.norm)))])

(define-named-type-alias CNothing (CU))
(define-named-type-alias Nothing (U))

(define-for-syntax (remove-Constant ty)
  (syntax-parse ty
    [(~Constant* t) #'t]
    [(~U* . tys) ; redo U reductions
     ((current-type-eval) #`(U . #,(stx-map remove-Constant #'tys)))]
    [(tycon . tys) 
     (transfer-stx-props #`(tycon . #,(stx-map remove-Constant #'tys)) ty)]
    [any ty]))
     
;; user-facing symbolic constant constructor: enforce non-concrete type
(define-syntax Constant
  (syntax-parser
    [(_ τ:type)
     #:fail-when (and (not (Term*? #'τ.norm)) #'τ)
     "Constant requires a symbolic term type"
     (syntax/loc this-syntax (Constant* τ.norm))]))

;; ---------------------------------

(define-base-types
  CAnyDeep CAny Any CBV CStx CSymbol CRegexp
  CSolution CSolver CPict
  COutputPort)

;; CVectorof includes all vectors
;; CIVectorof includes only immutable vectors
;; CMVectorof includes only mutable vectors
(define-type-constructor CIVectorof #:arity = 1)
(define-type-constructor CIBoxof #:arity = 1)
(define-type-constructor CISetof #:arity = 1)
(define-internal-type-constructor CMVectorof) ; #:arity = 1
(define-internal-type-constructor CMBoxof) ; #:arity = 1
(define-internal-type-constructor CMSetof) ; #:arity = 1

(define-typed-syntax (CMVectorof τ:type) ≫
  --------
  [⊢ (CMVectorof- τ.norm) ⇒ :: #%type])
(define-typed-syntax (CMBoxof τ:type) ≫
  --------
  [⊢ (CMBoxof- τ.norm) ⇒ :: #%type])
(define-typed-syntax (CMSetof τ:type) ≫
  --------
  [⊢ (CMSetof- τ.norm) ⇒ :: #%type])

;; TODO: Hash subtyping?
;; - invariant for now, like TR, though Rosette only uses immutable hashes?
(define-type-constructor CHashTable #:arity = 2)
(define-named-type-alias (CVectorof X) (CU (CIVectorof X) (CMVectorof X)))
(define-named-type-alias (CBoxof X) (CU (CIBoxof X) (CMBoxof X)))
(define-type-constructor CList #:arity >= 0)
(define-type-constructor CPair #:arity = 2)

(define-internal-type-constructor CVector) ; #:arity >= 0
(define-typed-syntax (CVector τ:type ...) ≫
  #:fail-when (stx-ormap (λ (τn τ) (and (concrete? τn) τ))
                         #'[τ.norm ...]
                         #'[τ ...])
  "Mutable locations must have types that allow for symbolic values"
  --------
  [⊢ (CVector- τ.norm ...) ⇒ :: #%type])

;; Struct
(define-internal-type-constructor Struct)

;; Struct types can't be single-shape types because struct inheritance exists.

(begin-for-syntax
  (struct typed-struct-info
    [transformer untyped-id predicate accessors field-types super-id no-super? some-mutable?]
    #:property prop:procedure (struct-field-index transformer)
    #:property prop:struct-info
    (λ (self)
      (extract-struct-info
       (syntax-local-value (typed-struct-info-untyped-id self)))))

  (define-syntax-class typed-struct-id
    #:attributes [[accessor 1] [τ_fld 1] [τ_fld_merged 1] super-id no-super? some-mutable?]
    [pattern (~var struct-id (local-value typed-struct-info?))
      #:with [accessor ...]
      (typed-struct-info-accessors (attribute struct-id.local-value))
      #:with [τ_fld ...]
      (typed-struct-info-field-types (attribute struct-id.local-value))
      #:with [τ_fld_merged ...]
      (stx-map type-merge #'[τ_fld ...] #'[τ_fld ...])
      #:attr no-super?
      (typed-struct-info-no-super? (attribute struct-id.local-value))
      #:attr super-id
      (typed-struct-info-super-id (attribute struct-id.local-value))
      #:attr some-mutable?
      (typed-struct-info-some-mutable? (attribute struct-id.local-value))]))

(define-typed-syntax Struct
  [(_ s:typed-struct-id τ:type ...) ≫
   #:fail-unless (stx-length=? #'[s.τ_fld_merged ...] #'[τ.norm ...])
   "wrong number of fields"
   [τ.norm τ⊑ s.τ_fld_merged] ...
   --------
   [⊢ (Struct- (quote-syntax- s) τ.norm ...)
      ⇒ :: #%type]])

;; ---------------------------------
;; Pattern Expanders for Types

;; C→* may be applied in both symbolic and concrete paths
;; C→** may be applied in only concrete paths
(define-internal-type-constructor C→*/internal) ; #:arity = 4
(define-internal-type-constructor C→**/internal) ; #:arity = 4
(define-internal-type-constructor MandArgs) ; #:arity >= 0
(define-internal-type-constructor OptKws) ; #:arity >= 1

(define-internal-type-constructor NoRestArg) ; #:arity = 0
(define-internal-type-constructor RestArg) ; #:arity = 1

(define-internal-type-constructor KwArg) ; #:arity = 2

(define-internal-type-constructor Result) ; #:arity = 3
(define-internal-type-constructor Prop/And) ; #:arity <= 0
(define-internal-type-constructor Prop/Or) ; #:arity <= 0
(define-internal-type-constructor Prop/IndexType) ; #:arity = 2
(define-internal-type-constructor Prop/IndexNotType) ; #:arity = 2
(define-internal-type-constructor Prop/ObjType) ; #:arity = 2
(define-internal-type-constructor Prop/ObjNotType) ; #:arity = 2

(define-syntax-parser Prop/Top [:id #'(Prop/And-)])
(define-syntax-parser Prop/Bot [:id #'(Prop/Or-)])
(define-syntax-parser @
  #:datum-literals [:]
  [(_ i:nat : τ:type)
   #'(Prop/IndexType- (quote- i) τ.norm)])
(define-syntax-parser !@
  #:datum-literals [:]
  [(_ i:nat : τ:type)
   #'(Prop/IndexNotType- (quote- i) τ.norm)])

(define-syntax-parser Prop/ObjType
  #:datum-literals [:]
  [(_ o : τ:type)
   #'(Prop/ObjType- o τ.norm)])
(define-syntax-parser Prop/ObjNotType
  #:datum-literals [:]
  [(_ o : τ:type)
   #'(Prop/ObjNotType- o τ.norm)])

(define-syntax-parser Prop
  [(_ p)
   (if (syntax-e #'p)
       #'p
       #'Prop/Top)])

(define-syntax-parser Prop/Or
  [(_ p ...)
   (if (stx-andmap syntax-e #'[p ...])
       #'(Prop/Or- p ...)
       #'Prop/Top)])
(define-syntax-parser Prop/And
  [(_ p ...)
   #:with [p* ...]
   (stx-filter syntax-e #'[p ...])
   #'(Prop/And- p* ...)])

(define-internal-type-constructor NoObj) ; #:arity = 0
(define-internal-type-constructor IdObj) ; #:arity = 1

(define-syntax-parser IdObj
  [(_ x:id) #`(IdObj- (quote-syntax-
                       #,(attach #'x 'orig-id (syntax-local-introduce #'x))))])

(begin-for-syntax
  (begin-for-syntax
    (define-syntax-class expr*
      [pattern (~and :expr (~not [:keyword . _]))]))
  (define-syntax-class expr*
    [pattern (~and :expr (~not [:keyword . _]))])

  (begin-for-syntax
    (define-splicing-syntax-class result-prop-pat
      #:datum-literals [:]
      [pattern (~seq) #:with pat_posprop #'_ #:with pat_negprop #'_]
      [pattern (~seq : #:+ pat_posprop #:- pat_negprop)]))
  (define-splicing-syntax-class result-prop
    #:datum-literals [:]
    [pattern (~seq) #:with posprop #'Prop/Top #:with negprop #'Prop/Top]
    [pattern (~seq : #:+ posprop #:- negprop)])

  (define-syntax ~C→
    (pattern-expander
     (syntax-parser
       [(_ pat_in:expr* ...
           (~and pat_out:expr* (~not (~literal ...)))
           props:result-prop-pat)
        #'(~C→* [pat_in ...] []
                pat_out
                : #:+ props.pat_posprop #:- props.pat_negprop)])))

  (define-syntax ~C→/conc
    (pattern-expander
     (syntax-parser
       [(_ pat_in:expr* ...
           (~and pat_out:expr* (~not (~literal ...)))
           props:result-prop-pat)
        #'(~C→** [pat_in ...] []
                pat_out
                : #:+ props.pat_posprop #:- props.pat_negprop)])))

  (define (convert-opt-kws opt-kws)
    (syntax-parse opt-kws
      [(~OptKws (~KwArg ((~literal quote-syntax) kw) τ) ...)
       #'[[kw τ] ...]]))

  (define-syntax ~C→*
    (pattern-expander
     (syntax-parser
       [(_ [pat_in:expr* ...] [pat_kw:expr ...] pat_out:expr*
           props:result-prop-pat)
        #:with opt-kws (generate-temporary 'opt-kws)
        #'(~C→*/internal
           (~MandArgs pat_in ...)
           (~and opt-kws
                 (~parse [pat_kw ...] (convert-opt-kws #'opt-kws)))
           (~NoRestArg)
           (~Result pat_out props.pat_posprop props.pat_negprop))]
       [(_ [pat_in:expr* ...] [pat_kw:expr ...] #:rest pat_rst:expr
           pat_out:expr*
           props:result-prop-pat)
        #:with opt-kws (generate-temporary 'opt-kws)
        #'(~C→*/internal
           (~MandArgs pat_in ...)
           (~and opt-kws
                 (~parse [pat_kw ...] (convert-opt-kws #'opt-kws)))
           (~RestArg pat_rst)
           (~Result pat_out props.pat_posprop props.pat_negprop))])))

  ;; more or less duplicates ~C→*
  (define-syntax ~C→**
    (pattern-expander
     (syntax-parser
       [(_ [pat_in:expr* ...] [pat_kw:expr ...] pat_out:expr*
           props:result-prop-pat)
        #:with opt-kws (generate-temporary 'opt-kws)
        #'(~C→**/internal
           (~MandArgs pat_in ...)
           (~and opt-kws
                 (~parse [pat_kw ...] (convert-opt-kws #'opt-kws)))
           (~NoRestArg)
           (~Result pat_out props.pat_posprop props.pat_negprop))]
       [(_ [pat_in:expr* ...] [pat_kw:expr ...] #:rest pat_rst:expr
           pat_out:expr*
           props:result-prop-pat)
        #:with opt-kws (generate-temporary 'opt-kws)
        #'(~C→**/internal
           (~MandArgs pat_in ...)
           (~and opt-kws
                 (~parse [pat_kw ...] (convert-opt-kws #'opt-kws)))
           (~RestArg pat_rst)
           (~Result pat_out props.pat_posprop props.pat_negprop))])))
  )

;; ---------------------------------
;; case-> and Ccase->

;; Ccase-> must check that its subparts are concrete function types
(define-syntax Ccase->
  (syntax-parser
    [(_ . tys)
     #:do [(define (concrete-function-type? τ)
             (or (C→/normal? τ) (C→*/internal? τ) (C→**/internal? τ)))]
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap concrete-function-type? #'tys+)
                   "Ccase-> require concrete function types"
     (syntax/loc this-syntax (Ccase->* . tys+))]))


;; TODO: What should case-> do when given symbolic function
;; types? Should it transform (case-> (U (C→ τ ...)) ...)
;; into (U (Ccase-> (C→ τ ...) ...)) ? What makes sense here?

;; ---------------------------------

(begin-for-syntax
  (define (add-pred stx pred)
    (set-stx-prop/preserved stx 'pred pred))
  (define (get-pred stx)
    (syntax-property stx 'pred))
  (define (add-typefor stx t)
    (set-stx-prop/preserved stx 'typefor t))
  (define (get-typefor stx)
    (syntax-property stx 'typefor))
  (define (mark-solvable stx)
    (set-stx-prop/preserved stx 'solvable? #t))
  (define (set-solvable stx v)
    (set-stx-prop/preserved stx 'solvable? v))
  (define (solvable? stx)
    (syntax-property stx 'solvable?))
  (define (mark-function stx)
    (set-stx-prop/preserved stx 'function? #t))
  (define (set-function stx v)
    (set-stx-prop/preserved stx 'function? v))
  (define (function? stx)
    (syntax-property stx 'function?)))

(define-syntax-parser add-predm
  [(_ stx pred) (add-pred #'stx #'pred)])
(define-syntax-parser add-typeform
  [(_ stx t) (add-typefor #'stx #'t)])
(define-syntax-parser mark-solvablem
  [(_ stx) (mark-solvable #'stx)])
(define-syntax-parser mark-functionm
  [(_ stx) (mark-function #'stx)])

;; ---------------------------------
;; Concrete types

(define-named-type-alias CBool (add-predm (CU CFalse CTrue) concrete-boolean?))

(define-named-type-alias CNat (add-predm (CU CZero CPosInt) concrete-nonnegative-integer?))
(define-named-type-alias CInt (add-predm (CU CNegInt CNat) concrete-integer?))
(define-named-type-alias CNum (add-predm (CU CFloat CInt) concrete-real?))

(begin-for-syntax
  (define (concrete-type-solvable? τ)
    (or (concrete-type-solvable-base? τ)
        (syntax-parse τ
          [(~C→ (~and (~or (~U* τ_in) τ_in))
                ...
                (~or (~U* τ_out) τ_out))
           (stx-andmap type-solvable? #'[τ_in ... τ_out])]
          [_ #false])))

  (define typeCNothing ((current-type-eval) #'CNothing))
  (define typeCFalse ((current-type-eval) #'CFalse))
  (define typeCTrue ((current-type-eval) #'CTrue))
  (define typeCBool ((current-type-eval) #'CBool))
  (define typeCInt ((current-type-eval) #'CInt))
  (define typeCNum ((current-type-eval) #'CNum))
  (define typeCBV ((current-type-eval) #'CBV))

  ;; concrete-type-solvable-base? : Type -> Bool
  (define (concrete-type-solvable-base? τ)
    (or (typecheck? τ typeCBool)
        (typecheck? τ typeCInt)
        (typecheck? τ typeCNum)
        (typecheck? τ typeCBV)))

  ;; REMEMBER single shape types are types that don't produce unions when
  ;; merged with any value of the same type
  (define (concrete-type-single-shape τ)
    (cond [(typecheck? τ typeCBool) typeCBool]
          [(typecheck? τ typeCInt) typeCInt]
          [else
           (syntax-parse τ
             [(~CList x ...)
              #:with [[_ Any*] ...] #'[[x Any] ...]
              ((current-type-eval) #'(CList Any* ...))]
             [_ #false])]))

  ;; types-same-singleton? : Type Type -> Bool
  (define (types-same-singleton? a b)
    (cond [(typecheck? a typeCFalse)
           (typecheck? b typeCFalse)]
          [(typecheck? a typeCTrue)
           (typecheck? b typeCTrue)]
          [else
           #false]))

  ;; concrete/shallow-recur? : Type -> Bool
  (define (concrete/shallow-recur? t)
    (and (concrete? t)
         (syntax-parse t
           [(~Struct _ _ ...) #t]
           [(~CHashTable _ _) #t]
           [(~Any _ . tys)
            (stx-andmap concrete/shallow-recur? #'tys)]
           [_ #t])))
  )

;; ---------------------------------
;; Symbolic versions of types

(define-named-type-alias NegInt (add-predm (U (Term CNegInt)) negative-integer?))
(define-named-type-alias Zero (add-predm (U (Term CZero)) zero-integer?))
(define-named-type-alias PosInt (add-predm (U (Term CPosInt)) positive-integer?))
(define-named-type-alias Float (U (Term CFloat)))
(define-named-type-alias String (U CString))
(define-named-type-alias Unit (add-predm (U CUnit) ro:void?))
(define-named-type-alias (CParamof X) (Ccase-> (C→ X)
                                               (C→ X CUnit)))
(define-named-type-alias (Listof X) (U (CListof X)))
(define-named-type-alias (Vectorof X) (U (CVectorof X)))
(define-named-type-alias (MVectorof X) (U (CMVectorof X)))
(define-named-type-alias (IVectorof X) (U (CIVectorof X)))
(define-named-type-alias (MBoxof X) (U (CMBoxof X)))
(define-named-type-alias (IBoxof X) (U (CIBoxof X)))
(define-named-type-alias (Pair X Y) (U (CPair X Y)))

(define-syntax →
  (syntax-parser
    [(_ ty ...+)
     #:with Cτ ((current-type-eval) #'(C→ ty ...))
     (add-orig
      (if (type-solvable? #'Cτ)
          #`(U (Term Cτ))
          #`(U Cτ))
      this-syntax)]))

(define-syntax →/conc
  (syntax-parser
    [(_ ty ...+)
     #:with Cτ ((current-type-eval) #'(C→/conc ty ...))
     (add-orig
      (if (type-solvable? #'Cτ)
          #`(U (Term Cτ))
          #`(U Cτ))
      this-syntax)]))

(define-named-type-alias True (U (Term CTrue)))
(define-named-type-alias False (U (Term CFalse)))
(define-named-type-alias Bool (add-predm (U (Term CBool)) ro:boolean?))
(define-named-type-alias Nat (add-predm (U (Term CNat)) nonnegative-integer?))

(define-named-type-alias Int (add-predm (U (Term CInt)) ro:integer?))
(define-named-type-alias Num (add-predm (U (Term CNum)) ro:real?))

(define-named-type-alias BV (add-predm (U (Term CBV)) ro:bv?))

(define-named-type-alias Solvable (U Bool Int Num BV))

(define-named-type-alias CAsserts (CListof Bool))

;; ---------------------------------------------------------

(define-type-constructor CSequenceof #:arity = 1)
(define-type-constructor CStructTypeProp #:arity = 1)

;; ---------------------------------------------------------

;; Function Types

(begin-for-syntax
  (define (C→? τ)
    (or (C→*/internal? τ) (C→**/internal? τ)))
  (define (concrete-function-type? τ)
    (or (C→? τ) (Ccase->? τ))))

;; (C→* mandatory-args optional-kws output)
;; (C→* mandatory-args optional-kws #:rest rest output)
;;   mandatory-args ::= [τ ...]
;;     optional-kws ::= [[kw τ] ...]
;;             rest ::= τ
;;           output ::= τ
(define-typed-syntax C→*
  [(_ [τ_in:expr* ...] [[kw:keyword τ_kw:expr*] ...] τ_out:expr*
      props:result-prop) ≫
   [⊢ [τ_in ≫ τ_in- ⇐ :: #%type] ...]
   [⊢ [τ_kw ≫ τ_kw- ⇐ :: #%type] ...]
   [⊢ τ_out ≫ τ_out- ⇐ :: #%type]
   --------
   [⊢ (C→*/internal- (MandArgs- τ_in- ...)
                     (OptKws- (KwArg- (quote-syntax kw) τ_kw-) ...)
                     (NoRestArg-)
                     (Result- τ_out- props.posprop props.negprop))
      ⇒ :: #%type]]
  [(_ [τ_in:expr* ...] [[kw:keyword τ_kw:expr*] ...] #:rest τ_rst
      τ_out:expr*
      props:result-prop) ≫
   [⊢ [τ_in ≫ τ_in- ⇐ :: #%type] ...]
   [⊢ [τ_kw ≫ τ_kw- ⇐ :: #%type] ...]
   [⊢ τ_rst ≫ τ_rst- ⇐ :: #%type]
   [⊢ τ_out ≫ τ_out- ⇐ :: #%type]
   --------
   [⊢ (C→*/internal- (MandArgs- τ_in- ...)
                     (OptKws- (KwArg- (quote-syntax kw) τ_kw-) ...)
                     (RestArg- τ_rst-)
                     (Result- τ_out- props.posprop props.negprop))
      ⇒ :: #%type]])

;; C→** may be applied only in concrete paths
;; more or less duplicates C→*
(define-typed-syntax C→**
  [(_ [τ_in:expr* ...] [[kw:keyword τ_kw:expr*] ...] τ_out:expr*
      props:result-prop) ≫
   [⊢ [τ_in ≫ τ_in- ⇐ :: #%type] ...]
   [⊢ [τ_kw ≫ τ_kw- ⇐ :: #%type] ...]
   [⊢ τ_out ≫ τ_out- ⇐ :: #%type]
   --------
   [⊢ (C→**/internal- (MandArgs- τ_in- ...)
                     (OptKws- (KwArg- (quote-syntax kw) τ_kw-) ...)
                     (NoRestArg-)
                     (Result- τ_out- props.posprop props.negprop))
      ⇒ :: #%type]]
  [(_ [τ_in:expr* ...] [[kw:keyword τ_kw:expr*] ...] #:rest τ_rst
      τ_out:expr*
      props:result-prop) ≫
   [⊢ [τ_in ≫ τ_in- ⇐ :: #%type] ...]
   [⊢ [τ_kw ≫ τ_kw- ⇐ :: #%type] ...]
   [⊢ τ_rst ≫ τ_rst- ⇐ :: #%type]
   [⊢ τ_out ≫ τ_out- ⇐ :: #%type]
   --------
   [⊢ (C→**/internal- (MandArgs- τ_in- ...)
                     (OptKws- (KwArg- (quote-syntax kw) τ_kw-) ...)
                     (RestArg- τ_rst-)
                     (Result- τ_out- props.posprop props.negprop))
      ⇒ :: #%type]])

(define-typed-syntax C→
  [(_ τ_in:expr* ... [kw:keyword τ_kw:expr*] ... τ_out:expr*) ≫
   --------
   [≻ (C→* [τ_in ...] [[kw τ_kw] ...] τ_out)]])

(define-typed-syntax C→/conc
  [(_ τ_in:expr* ... [kw:keyword τ_kw:expr*] ... τ_out:expr*) ≫
   --------
   [≻ (C→** [τ_in ...] [[kw τ_kw] ...] τ_out)]])

;; ---------------------------------------------------------

;; Extra convenience types for predicates

(define-named-type-alias LiftedPred (Ccase-> (C→ CAny CBool)
                                             (C→ Any Bool)))
(define-named-type-alias LiftedPredDeep (Ccase-> (C→ CAnyDeep CBool)
                                                 (C→ Any Bool)))
(define-named-type-alias LiftedPred2 (Ccase-> (C→ CAny CAny CBool)
                                              (C→ Any Any Bool)))
(define-named-type-alias LiftedPredDeep2 (Ccase-> (C→ CAnyDeep CAnyDeep CBool)
                                                  (C→ Any Any Bool)))
(define-named-type-alias LiftedNumPred (Ccase-> (C→ CNum CBool)
                                                (C→ Num Bool)))
(define-named-type-alias LiftedIntPred (Ccase-> (C→ CInt CBool)
                                                (C→ Int Bool)))
(define-named-type-alias UnliftedPred (C→ Any CBool))

(define-named-type-alias CBVPred LiftedPred)
(define-named-type-alias BVPred (add-predm (U LiftedPred) lifted-bitvector?))

(define-simple-macro (LiftedPredFor τ:type)
  (Ccase-> (C→* [CAny] [] CBool : #:+ (@ 0 : τ.norm) #:- (!@ 0 : τ.norm))
           (C→* [Any] [] Bool : #:+ (@ 0 : τ.norm) #:- (!@ 0 : τ.norm))))

(define-simple-macro (UnliftedPredFor τ:type)
  (C→* [Any] [] CBool : #:+ (@ 0 : τ.norm) #:- (!@ 0 : τ.norm)))

;; ---------------------------------------------------------

;; Merging

;; Merging for values:
;;   sameBaseSingleShape(u, v) :=
;;     (isBool(v) and isBool(u)) or (isInt(v) and isInt(u))
;;   sameListSingleShape(u, v) :=
;;     isList(v) and isList(u) and (len(v) = len(u))
;;   samePtr(u, v) :=
;;     u = v
;;   sameSingleShape(u, v) :=
;;     samePtr(u, v) or sameBaseSingleShape(u, v) or sameListSingleShape
;;   μ(u, v) :=
;;     / u                   if u = v
;;     | (ite _ u v)         if sameBaseSingleShape(u, v)
;;     | (list w_0 ... w_n)  if sameListSingleShape(u, v) and
;;     |                        w_i = μ(u[i], v[i]) for 0 <= i < len
;;     | μ(v, u)            if not isUnion(u) and isUnion(v)
;;     | (union u v)         if isUnion(u), not isUnion(v), and
;;     |                        !∃(u_i ∈ contents(u)) sameSingleShape(u_i, v)
;;    <  (union u' v')       if isUnion(u), not isUnion(v),
;;     |                        u_i ∈ contents(u), sameSingleShape(u_i, v),
;;     |                        u' = remove(u_i, u), and
;;     |                        v' = μ(u_i, v)
;;     | (union w u' v')     if isUnion(u), isUnion(v),
;;     |                        w = (union μ(u_i, v_j) ...) where sameSingleShape(u_i, v_i),
;;     |                        u' = (union u_i ...) where !∃(v_j) sameSingleShape(u_i, v_j), and
;;     |                        v' = (union v_j ...) where !∃(u_i) sameSingleShape(u_i, v_j)
;;     \ (union u v)         otherwise

;; Merging for types:
;; All *base* single-shape types must be solvable.
;; All singleton types must have the property that ∀a:τ.∀b:τ.(rkt:eq? a b)
;;   μ(u, v) :=
;;     / u                   if sameSingletonType(u, v)
;;     | (Term (CU u v))     if sameBaseSingleShape(u, v)
;;     | (List w_0 ... w_n)  if sameListSingleShape(u, v) and
;;     |                        w_i = μ(u[i], v[i]) for 0 <= i < len
;;     | μ(v, u)            if not isUnion(u) and isUnion(v)
;;     | (U u v)             if isUnion(u), not isUnion(v), and
;;     |                        !∃(u_i ∈ contents(u)) sameSingleShape(u_i, v)
;;     | (U u' v')           if isUnion(u), not isUnion(v),
;;     |                        u_i ∈ contents(u), sameSingleShape(u_i, v),
;;    <                         u' = remove(u_i, u), and
;;     |                        v' = μ(u_i, v)
;;     | (U w u' v')         if isUnion(u), isUnion(v),
;;     |                        w = (U μ(u_i, v_j) ...) where sameSingleShape(u_i, v_i),
;;     |                        u' = (U u_i ...) where !∃(v_j) sameSingleShape(u_i, v_j), and
;;     |                        v' = (U v_j ...) where !∃(u_i) sameSingleShape(u_i, v_j)
;;     | (U u v)             if isSingleShape(u), isSingleShape(v), and
;;     |                        !sameSingleShape(u, v)
;;     \ ???                 otherwise

;; What to do for the else case? Need some more complicated merging, using
;; both a U on the outside and possibly more merges in sub-parts.

(begin-for-syntax
  ;; Un? : Type -> Bool
  (define (Un? τ)
    (or (U*? τ) (CU*? τ)))

  ;; U-contents : Type -> (Listof Type)
  (define (U-contents τ)
    (syntax-parse τ
      [(~U* contents ...)
       (attribute contents)]
      [(~CU* contents ...)
       (attribute contents)]))

  ;; types-same-single-shape 
  (define (types-same-single-shape a b)
    (let ([a-shape (type-single-shape a)])
      (and a-shape
           (let ([b-shape (type-single-shape b)])
             (and (type=? a-shape b-shape)
                  a-shape)))))

  ;; type-merge : Type Type -> Type
  (define (type-merge a b)
    (cond [(types-same-singleton? a b) a]
          [(typecheck? a typeCNothing) b]
          [(typecheck? b typeCNothing) a]
          [else
           ;; Here it will result in some kind of term or union,
           ;; so remove immediate Constant wrappers
           (define a* (syntax-parse a [(~Constant* a*) #'a*] [_ a]))
           (define b* (syntax-parse b [(~Constant* b*) #'b*] [_ b]))
           (type-merge/non-singleton a* b*)]))

  ;; type-merge/non-singleton : Type Type -> Type
  (define (type-merge/non-singleton a b)
    ;; if they are both single-shape and their shapes are
    ;; the same,
    (define single-shape (types-same-single-shape a b))
    (cond [single-shape
           (cond
             [(type-solvable? single-shape)
              (type-merge/single-shape-solvable a b)]
             [else
              (syntax-parse (list a b)
                ;; this works because CList is covariant in all
                ;; the elements
                [[(~CList a ...) (~CList b ...)]
                 #:with [ab ...] (stx-map type-merge #'[a ...] #'[b ...])
                 ((current-type-eval) #'(CList ab ...))])])]
          ;; if they are both single shape but their shapes
          ;; are different, then safe to combine with U
          ;; because they will never combine into terms
          [(and (type-single-shape? a) (type-single-shape? b))
           ((current-type-eval) #`(U #,a #,b))]
          ;; if they are both solvable but they are not single-shape
          ;; then they could combine with either terms or unions
          [(and (type-solvable? a) (type-solvable? b))
           (define a* (syntax-parse a [(~Term* a*) #'a*] [_ a]))
           (define b* (syntax-parse b [(~Term* b*) #'b*] [_ b]))
           (define ab* ((current-type-eval) #`(CU #,a* #,b*)))
           ((current-type-eval)
            (cond [(type-solvable? ab*) #`(U (Term #,ab*))]
                  [else #`(U #,a #,b)]))]
          [(and (not (Un? a)) (Un? b))
           (type-merge b a)]
          [(and (Un? a) (not (Un? b)))
           (type-merge/U/not-U (U-contents a) b)]
          [(and (Un? a) (Un? b))
           (type-merge/U/U (U-contents a) (U-contents b))]
          ;; otherwise, some more complicated merging is
          ;; needed, using both a U on the outside and
          ;; possibly more merges in sub-parts
          [(and (Struct? a) (Struct? b))
           (syntax-parse (list a b)
             #:literals [quote-syntax-]
             [[(~Struct (quote-syntax- sa:id) τa ...)
               (~Struct (quote-syntax- sb:id) τb ...)]
              #:when (free-identifier=? #'sa #'sb)
              #:with [τab ...] (stx-map type-merge #'[τa ...] #'[τb ...])
              ((current-type-eval) #'(U (Struct sa τab ...)))]
             [_
              ;; TODO: do some merging within if they are related by
              ;; sub-structing
              ((current-type-eval) #`(U #,a #,b))])]
          [else
           ;; TODO: do some merging within
           ((current-type-eval) #`(U #,a #,b))]))

  ;; type-merge/single-shape-solvable : Type Type -> Type
  (define (type-merge/single-shape-solvable a b)
    ((current-type-eval)
     (cond [(typecheck? a b)
            #`(Term #,b)]
           [(typecheck? b a)
            #`(Term #,a)]
           [else
            (define a* (syntax-parse a [(~Term* a*) #'a*] [_ a]))
            (define b* (syntax-parse b [(~Term* b*) #'b*] [_ b]))
            #`(Term (CU #,a* #,b*))])))

  ;; type-merge/U/not-U : (Listof Type) Type -> Type
  (define (type-merge/U/not-U as b)
    (define-values [as/b-shape as/without]
      (partition (λ (a) (types-same-single-shape a b)) as))
    (define b/with
      (for/fold ([b b])
                ([a (in-list as/b-shape)])
        (type-merge a b)))
    ((current-type-eval) #`(U #,@as/without #,b/with)))

  ;; type-merge/U/U : (Listof Type) (Listof Type) -> Type
  (define (type-merge/U/U as bs)
    (define same-shapes
      (for*/list ([a (in-list as)]
                  [b (in-list bs)]
                  #:when (types-same-single-shape a b))
        (type-merge a b)))
    (define as/without
      (filter (λ (a) (not (ormap (λ (b) (types-same-single-shape a b)) bs)))
              as))
    (define bs/without
      (filter (λ (b) (not (ormap (λ (a) (types-same-single-shape a b)) as)))
              bs))
    ((current-type-eval) #`(U #,@same-shapes #,@as/without #,@ bs/without)))

  ;; type-merge* : (StxListof Type) -> Type
  (define (type-merge* τs)
    (cond
      [(stx-null? τs) ((current-type-eval) #'Nothing)]
      [else
       (for/fold ([acc (stx-car τs)])
                 ([b (in-list (stx->list (stx-cdr τs)))])
         (type-merge acc b))]))
  )

;; ---------------------------------------------------------

;; Instantiating Propositions for Occurrence Typing

(begin-for-syntax
  (define propProp/Top ((current-type-eval) #'Prop/Top))

  ;; prop-instantitate : (Listof ObjStx) -> [PropStx -> PropStx]
  (define (prop-instantiate arg-objs)
    (define (inst p)
      (syntax-parse (if (syntax-e p) p propProp/Top)
        #:literals [quote-]
        [(~Prop/And q ...)
         #`(Prop/And- #,@(stx-map inst #'[q ...]))]
        [(~Prop/Or q ...)
         #`(Prop/Or- #,@(stx-map inst #'[q ...]))]
        [(~Prop/IndexType (quote- i:nat) τ)
         (syntax-parse (list-ref arg-objs (syntax-e #'i))
           [(~NoObj) #`Prop/Top]
           [obj #`(Prop/ObjType- obj τ)])]
        [(~Prop/IndexNotType (quote- i:nat) τ)
         (syntax-parse (list-ref arg-objs (syntax-e #'i))
           [(~NoObj) #`Prop/Top]
           [obj #`(Prop/ObjNotType- obj τ)])]
        [(~Prop/ObjType _ _) p]
        [(~Prop/ObjNotType _ _) p]))
    inst)

  ;; get-arg-obj : Stx -> ObjStx
  (define (get-arg-obj stx)
    ((current-type-eval)
     (syntax-parse stx
       [x:id #:do [(define x* (detach #'x 'orig-binding))]
             #:when x*
             ;; syntax-local-introduce ruins it
             #`(IdObj- (quote-syntax-
                        #,(attach
                           (attach x* 'orig-id x*)
                           'orig-type (typeof #'x))))]
       [_ #'(NoObj-)])))

  ;; prop->env : PropStx -> (Maybe (Listof (List Id Type)))
  (define (prop->env p)
    (define env
      (prop->env/acc p (make-immutable-free-id-table)))
    (and env (free-id-table-map env list)))

  ;; prop->env/acc : PropStx (FreeIdTableof Type) -> (Maybe (FreeIdTableof Type))
  (define (prop->env/acc p acc)
    (syntax-parse (if (syntax-e p) p propProp/Top)
      #:literals [quote-syntax-]
      [(~Prop/And q ...)
       (for/fold ([acc acc]) ([q (in-list (stx->list #'[q ...]))])
         #:break (false? acc)
         (prop->env/acc q acc))]
      [(~Prop/Or q)
       #false]
      [(~Prop/Or q ...)
       (for/fold ([sub #false])
                 ([q (in-list (stx->list #'[q ...]))])
         (occurrence-env-id-table-or
          sub
          (prop->env/acc q acc)))]
      [(~Prop/ObjType o τ)
       (syntax-parse #'o
         #:literals [quote-syntax-]
         [(~NoObj) acc]
         [(~IdObj (quote-syntax- x:id))
          (define x* (syntax-local-introduce (detach #'x 'orig-id)))
          (define τ_orig (free-id-table-ref acc x* (λ () (detach #'x 'orig-type))))
          (define τ_new (type-restrict τ_orig #'τ))
          (if (typecheck? τ_new typeCNothing)
              #false
              (free-id-table-set acc x* τ_new))])]
      [(~Prop/ObjNotType o τ)
       (syntax-parse #'o
         #:literals [quote-syntax-]
         [(~NoObj) acc]
         [(~IdObj (quote-syntax- x:id))
          (define x* (syntax-local-introduce (detach #'x 'orig-id)))
          (define τ_orig (free-id-table-ref acc x* (λ () (detach #'x 'orig-type))))
          (define τ_new (type-remove τ_orig #'τ))
          (if (typecheck? τ_new typeCNothing)
              #false
              (free-id-table-set acc x* τ_new))])]))

  ;; type-restrict : Type Type -> Type
  (define (type-restrict orig new)
    (cond [(types-no-overlap? orig new) typeCNothing]
          [(typecheck? new orig) new]
          [(Un? new)
           ((current-type-eval)
            (syntax-parse new
              [(~CU* n ...)
               #`(CU #,@(for/list ([n (in-list (stx->list #'[n ...]))])
                          (type-restrict orig n)))]
              [(~U* n ...)
               (define ns*
                 (for/list ([n (in-list (stx->list #'[n ...]))])
                   (type-restrict orig n)))
               (cond
                 [(and (concrete? orig) (andmap concrete? ns*))
                  #`(CU #,@ns*)]
                 [else
                  #`(U #,@ns*)])]))]
          [(Term*? new)
           (syntax-parse new
             [(~Term* n)
              (define n* (type-restrict orig #'n))
              (cond
                [(concrete? orig) n*]
                [else ((current-type-eval) #`(Term #,n*))])])]
          [(Un? orig)
           ((current-type-eval)
            (syntax-parse orig
              [(~CU* o ...)
               #`(CU #,@(for/list ([o (in-list (stx->list #'[o ...]))])
                          (type-restrict o new)))]
              [(~U* o ...)
               ;; TODO: What does a U type mean, and can we safely reduce
               ;; cases within U types?
               (define os*
                 (for/list ([o (in-list (stx->list #'[o ...]))])
                   (type-restrict o new)))
               (cond
                 [(and (concrete? new) (andmap concrete? os*))
                  #`(CU #,@os*)]
                 [else
                  #`(U #,@os*)])]))]
          [(Term*? orig)
           (syntax-parse orig
             [(~Term* o)
              (define o* (type-restrict #'o new))
              (cond
                [(concrete? new) o*]
                [else ((current-type-eval) #`(Term #,o*))])])]
          [else
           (syntax-parse (list orig new)
             #:literals [quote-syntax-]
             [[(~Struct (quote-syntax- sa:typed-struct-id) τa ...)
               (~Struct (quote-syntax- sb:typed-struct-id) τb ...)]
              #:when (and (free-identifier=? #'sa #'sb)
                          (not (attribute sa.some-mutable?)))
              #:with [τab ...] (stx-map type-restrict #'[τa ...] #'[τb ...])
              ((current-type-eval) #'(Struct sa τab ...))]
             [_
              (printf "refine-type:\n  orig: ~a\n  new:  ~a\n"
                      (type->str orig)
                      (type->str new))
              new])]))

  ;; type-remove : Type Type -> Type
  (define (type-remove orig new-not)
    (cond [(typecheck? orig new-not) typeCNothing]
          [(Un? orig)
           ((current-type-eval)
            (syntax-parse orig
              [(~CU* o ...)
               #`(CU #,@(for/list ([o (in-list (stx->list #'[o ...]))])
                          (type-remove o new-not)))]
              [(~U* o ...)
               ;; TODO: What does a U type mean, and can we safely remove
               ;; from cases of U types?
               (define os*
                 (for/list ([o (in-list (stx->list #'[o ...]))])
                   (type-remove o new-not)))
               #`(U #,@os*)]))]
          [(Term*? orig)
           (syntax-parse orig
             [(~Term* o)
              (define o* (type-remove #'o new-not))
              ((current-type-eval) #`(Term #,o*))])]
          [(types-no-overlap? orig new-not)
           orig]
          [else
           ;; Probably nothing more we can do in the current system
           orig]))

  ;; types-no-overlap? : Type Type -> Bool
  (define (types-no-overlap? a b)
    (syntax-parse (list a b)
      #:literals [quote-syntax-]
      [[~CPosInt
        (~or ~CZero ~CNegInt ~CString ~CTrue ~CFalse (~Struct _ _ ...))]
       #true]
      [[~CZero
        (~or ~CPosInt ~CNegInt ~CString ~CTrue ~CFalse (~Struct _ _ ...))]
       #true]
      [[~CNegInt
        (~or ~CPosInt ~CZero ~CString ~CTrue ~CFalse (~Struct _ _ ...))]
       #true]
      [[~CString
        (~or ~CPosInt ~CZero ~CNegInt ~CTrue ~CFalse (~Struct _ _ ...))]
       #true]
      [[~CTrue
        (~or ~CPosInt ~CZero ~CNegInt ~CString ~CFalse (~Struct _ _ ...))]
       #true]
      [[~CFalse
        (~or ~CPosInt ~CZero ~CNegInt ~CString ~CTrue (~Struct _ _ ...))]
       #true]
      [[(~Struct _ _ ...)
        (~or ~CPosInt ~CZero ~CNegInt ~CString ~CTrue ~CFalse)]
       #true]
      [[(~Struct (quote-syntax- sa:id) _ ...)
        (~Struct (quote-syntax- sb:id) _ ...)]
       (structs-no-overlap? #'sa #'sb)]
      [else #false]))

  ;; structs-no-overlap? : StructId StructId -> Bool
  (define (structs-no-overlap? a b)
    (syntax-parse (list a b)
      [[sa:typed-struct-id sb:typed-struct-id]
       (cond
         [(free-identifier=? #'sa #'sb) #false]
         [(and (attribute sa.no-super?)
               (attribute sb.no-super?))
          #true]
         [(attribute sa.no-super?)
          (structs-no-overlap? #'sa #'sb.super-id)]
         [(attribute sb.no-super?)
          (structs-no-overlap? #'sa.super-id #'sb)]
         [else
          (structs-no-overlap? #'sa.super-id #'sb.super-id)])]))

  ;; sub-struct? : StructId StructId -> Bool
  (define (sub-struct? a b)
    (syntax-parse (list a b)
      [[sa:typed-struct-id sb:typed-struct-id]
       (cond
         [(free-identifier=? #'sa #'sb) #true]
         [(attribute sa.no-super?) #false]
         [else
          (sub-struct? #'sa.super-id #'sb)])]))

  ;; occurrence-env-id-table-or :
  ;; (Maybe (FreeIdTableof Type)) (Maybe (FreeIdTableof Type)) -> (Maybe (FreeIdTableof Type))
  ;; Combines two possible occurrence-typing type environments with or.
  ;; This means we don't know which environment will be true, so the result
  ;; will only include identifiers that are included in both environments,
  ;; with the types that are a union of the associated types in both.
  (define (occurrence-env-id-table-or a b)
    (cond [(false? a) b]
          [(false? b) a]
          [else
           (for/fold ([a a])
                     ([(id τ_b) (in-free-id-table b)])
             (cond
               [(dict-has-key? a id)
                (free-id-table-update
                 a
                 id
                 (λ (τ_a) (type-or τ_a τ_b)))]
               [else
                (free-id-table-remove a id)]))]))

  ;; type-or : Type Type -> Type
  (define (type-or a b)
    (cond [(and (concrete? a) (concrete? b))
           ((current-type-eval) #`(CU #,a #,b))]
          [else
           ((current-type-eval) #`(U #,a #,b))]))

  (define-syntax-class occurrence-env
    #:attributes [[x 1] [τ 1] bottom?]
    [pattern #false
             #:attr bottom? #true
             #:with [[x τ] ...] #'[]]
    [pattern [[x τ] ...]
             #:attr bottom? #false])
  )

;; (with-occurrence-env occurrence-env expr)
(define-typed-syntax with-occurrence-env
  [(_ #false body:expr) ≫
   #:with DEAD (syntax/loc #'body
                 (ro:assert #false "this should be dead code"))
   --------
   [⊢ DEAD (⇒ : CNothing) (⇒ prop+ Prop/Bot) (⇒ prop- Prop/Bot)]]
  [(_ ([x:id τ:expr] ...) body:expr) ⇐ τ_body ≫
   #:do [(define scope
           (make-syntax-delta-introducer (datum->syntax #'body '||) #f))]
   #:with [x* ...] (scope #'[x ...])
   [[x* ≫ x- : τ] ... ⊢ body ≫ body- ⇐ τ_body]
   --------
   [⊢ (let- ([x- x] ...) body-)]]
  [(_ ([x:id τ:type] ...) body:expr) ≫
   #:do [(define scope
           (make-syntax-delta-introducer (datum->syntax #'body '||) #f))]
   #:with [x* ...] (scope #'[x ...])
   [[x* ≫ x- : τ] ... ⊢ body ≫ body-
                  (⇒ : τ_body)
                  (⇒ prop+ p+)
                  (⇒ prop- p-)]
   --------
   [⊢ (let- ([x- x] ...) body-)
      (⇒ : τ_body)
      (⇒ prop+ (Prop p+))
      (⇒ prop- (Prop p-))]])

;; (with-occurrence-prop prop expr)
(define-syntax-parser with-occurrence-prop
  [(_ prop:expr body:expr)
   #:with env:occurrence-env
   (prop->env (expand/df (if (syntax-e #'prop) #'prop #'Prop/Top)))
   #'(with-occurrence-env env body)])

;; ---------------------------------------------------------

;; Subtyping

(begin-for-syntax
  (define (sub? t1 t2)
    ; need this because recursive calls made with unexpanded types
   ;; (define τ1 ((current-type-eval) t1))
   ;; (define τ2 ((current-type-eval) t2))
    ;; (printf "t1 = ~a\n" (syntax->datum t1))
    ;; (printf "t2 = ~a\n" (syntax->datum t2))
    (or 
     (Any? t2)
     (and (concrete/shallow-recur? t1) (CAny? t2))
     (and (concrete/recur? t1) (CAnyDeep? t2))
     ((current-type=?) t1 t2)
     (syntax-parse (list t1 t2)
       #:literals [quote-syntax-]
       ;; Constant clause must appear before U, ow (Const Int) <: Int wont hold
       [((~Constant* ty1) (~Constant* ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~Constant* ty) _) 
        (typecheck? #'ty t2)]
       ; term types
       [((~Term* ty1) (~Term* ty2))
        (typecheck? #'ty1 #'ty2)]
       [(ty1 (~Term* ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CListof ty1) (~CListof ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CList . tys1) (~CList . tys2))
        (and (stx-length=? #'tys1 #'tys2)
             (typechecks? #'tys1 #'tys2))]
       [((~CList . tys) (~CListof ty))
        (for/and ([t (stx->list #'tys)])
          (typecheck? t #'ty))]
       ;; vectors, only immutable vectors are covariant
       [((~CIVectorof ty1) (~CIVectorof ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CIBoxof ty1) (~CIBoxof ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CPair ty1a ty1b) (~CPair ty2a ty2b))
        (and (typecheck? #'ty1a #'ty2a)
             (typecheck? #'ty1b #'ty2b))]
       ;; structs, if they are immutable, they are covariant
       [((~Struct (quote-syntax- sa:typed-struct-id) τa ...)
         (~Struct (quote-syntax- sb:typed-struct-id) τb ...))
        #:when (sub-struct? #'sa #'sb)
        #:when (and (not (attribute sa.some-mutable?))
                    (not (attribute sb.some-mutable?)))
        (define n (stx-length #'[τb ...]))
        (typechecks? (take (stx->list #'[τa ...]) n) #'[τb ...])]
       ; 2 U types, subtype = subset
       [((~CU* . ts1) _)
        (for/and ([t (stx->list #'ts1)])
          (typecheck? t t2))]
       [((~U* . ts1) _)
        (and
         (or (Any? t2) (U*? t2))
         (for/and ([t (stx->list #'ts1)])
           (typecheck? t t2)))]
       ; 1 U type, 1 non-U type. subtype = member
       [(_ (~CU* . ts2))
        #:when (not (or (U*? t1) (CU*? t1)))
        (for/or ([t (stx->list #'ts2)])
          (typecheck? t1 t))]
       [(_ (~U* . ts2))
        #:when (not (or (U*? t1) (CU*? t1)))
        (for/or ([t (stx->list #'ts2)])
          (typecheck? t1 t))]
       ; 2 case-> types, subtype = subset
       [(_ (~Ccase-> . ts2))
        (for/and ([t (stx->list #'ts2)])
          (typecheck? t1 t))]
       ; 1 case-> , 1 non-case->
       [((~Ccase-> . ts1) _)
        (for/or ([t (stx->list #'ts1)])
          (typecheck? t t2))]
       [((~C→ s1 ... s2 : #:+ sp+ #:- sp-)
         (~C→ t1 ... t2 : #:+ tp+ #:- tp-))
        (and (typechecks? #'(t1 ...) #'(s1 ...))
             (typecheck? #'s2 #'t2)
             (prop-implies? #'sp+ #'tp+)
             (prop-implies? #'sp- #'tp-))]
       [((~C→/conc s1 ... s2 : #:+ sp+ #:- sp-)
         (~or (~C→/conc t1 ... t2 : #:+ tp+ #:- tp-)
              (~C→ t1 ... t2 : #:+ tp+ #:- tp-)))
        (and (typechecks? #'(t1 ...) #'(s1 ...))
             (typecheck? #'s2 #'t2)
             (prop-implies? #'sp+ #'tp+)
             (prop-implies? #'sp- #'tp-))]
       [((~C→* [s1 ...] [] #:rest srst s2 : #:+ sp+ #:- sp-)
         (~C→* [t1 ...] []             t2 : #:+ tp+ #:- tp-))
        (define sn (stx-length #'[s1 ...]))
        (define-values [t1ns t1rs]
          (split-at (stx->list #'[t1 ...]) sn))
        (define t1r ((current-type-eval) #`(CList #,@t1rs)))
        (and (typechecks? t1ns #'(s1 ...))
             (typecheck? t1r #'srst)
             (typecheck? #'s2 #'t2)
             (prop-implies? #'sp+ #'tp+)
             (prop-implies? #'sp- #'tp-))]
       [((~C→* [s1 ...] [] #:rest srst s2 : #:+ sp+ #:- sp-)
         (~C→* [t1 ...] [] #:rest trst t2 : #:+ tp+ #:- tp-))
        (and (typechecks? #'(t1 ...) #'(s1 ...))
             (typecheck? #'trst #'srst)
             (typecheck? #'s2 #'t2)
             (prop-implies? #'sp+ #'tp+)
             (prop-implies? #'sp- #'tp-))]
       [_ #f])))
  (current-sub? sub?)
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2)))

  (define (prop-implies? p1 p2)
    (syntax-parse (list p1 p2)
      ;; anything implies true
      [[_ (~Prop/And)] #true]
      ;; false implies anything
      [[(~Prop/Or) _] #false]
      [[_ _]
       (cond [(type=? p1 p2) #true]
             [else #false])]))
  )

