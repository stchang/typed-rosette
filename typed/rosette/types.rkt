#lang turnstile

(provide CAny Any
         CNothing Nothing
         CU U
         Constant
         (for-syntax Any?
                     ~CU* ~U* CU*? U*?
                     ~Constant* Constant*? remove-Constant
                     concrete?)
         ;; Function types
         C→ C→* Ccase->
         →
         (for-syntax concrete-function-type?
                     ~C→ ~C→* ~Ccase->
                     C→? Ccase->?)
         ;; Parameters
         CParamof ; TODO: symbolic Param not supported yet
         ;; List types
         CListof CList CPair
         Listof Pair
         (for-syntax ~CListof ~CList ~CPair)
         ;; Other container types
         CHashTable
         CSequenceof
         CISetof CMSetof
         CBoxof CMBoxof CIBoxof MBoxof IBoxof
         CVectorof CMVectorof CIVectorof CVector
         Vectorof MVectorof IVectorof
         (for-syntax ~CHashTable
                     ~CSequenceof
                     ~CMBoxof ~CIBoxof
                     ~CMVectorof ~CIVectorof
                     ~CMSetof ~CISetof)
         ;; BV types
         CBV BV
         CBVPred BVPred
         ;; Structure Type Properties
         CStructTypeProp
         (for-syntax ~CStructTypeProp)
         ;; Other base types
         CUnit Unit
         CZero Zero
         CPosInt PosInt
         CNegInt NegInt
         CNat Nat
         CInt Int
         CFloat Float
         CNum Num
         CFalse CTrue CBool Bool
         CString String
         CStx
         CSymbol
         CAsserts
         COutputPort
         CSolution CSolver CPict CRegexp CSymbol
         LiftedPred LiftedPred2 LiftedNumPred LiftedIntPred UnliftedPred
         (for-syntax ~CUnit CUnit?
                     ~CString CString?
                     ~CTrue ~CFalse)
         ;; The relationship between types and
         ;; rosette's run-time type predicates
         add-predm
         add-typeform
         mark-solvablem
         mark-functionm
         (for-syntax get-pred))

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
           [~True ~CTrue] [~False ~CFalse]
           [~String ~CString]
           [~Unit ~CUnit])
         (only-in turnstile/examples/stlc+cons
           [List CListof] [~List ~CListof])
         (prefix-in ro: rosette)
         (prefix-in ro: rosette/lib/synthax)
         (rename-in "../rosette-util.rkt" [bitvector? lifted-bitvector?]))

;; ---------------------------------
;; Concrete and Symbolic union types

(begin-for-syntax
  (define (concrete? t)
    (not (or (Any? t) (U*? t) (Constant*? t))))
  (define (concrete/recur? t)
    (and (concrete? t)
         (syntax-parse t
           [(~Any _ . tys)
            (stx-andmap concrete/recur? #'tys)]
           [_ #t]))))

(define-base-types
  CAny Any CBV CStx CSymbol CRegexp
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
  #:fail-when (and (concrete? #'τ.norm) #'τ)
  "Mutable locations must have types that allow for symbolic values"
  --------
  [⊢ (CMVectorof- τ.norm) ⇒ :: #%type])
(define-typed-syntax (CMBoxof τ:type) ≫
  #:fail-when (and (concrete? #'τ.norm) #'τ)
  "Mutable locations must have types that allow for symbolic values"
  --------
  [⊢ (CMBoxof- τ.norm) ⇒ :: #%type])
(define-typed-syntax (CMSetof τ:type) ≫
  #:fail-when (and (concrete? #'τ.norm) #'τ)
  "Mutable locations must have types that allow for symbolic values"
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

;; TODO: update orig to use reduced type
(define-syntax (CU stx)
  (syntax-parse stx
    [(_ . tys)
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap concrete? #'tys+)
                   "CU requires concrete types"
     #'(CU* . tys+)]))

;; internal symbolic union constructor
(define-type-constructor U* #:arity >= 0)

;; user-facing symbolic U constructor: flattens and prunes
(define-syntax (U stx)
  (syntax-parse stx
    [(_ . tys)
     ;; canonicalize by expanding to U*, with only (sorted and pruned) leaf tys
     #:with ((~or (~U* ty1- ...) (~CU* ty2- ...) ty3-) ...) (stx-map (current-type-eval) #'tys)
     #:with tys- (prune+sort #'(ty1- ... ... ty2- ... ... ty3- ...))
     #'(U* . tys-)]))

(define-named-type-alias CNothing (CU))
(define-named-type-alias Nothing (U))

;; internal symbolic constant constructor
(define-type-constructor Constant* #:arity = 1)

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
    [(_ τ)
     #:with τ+ ((current-type-eval) #'τ)
     #:fail-when (and (concrete? #'τ+) #'τ)
     "Constant requires a symbolic type"
     #'(Constant* τ+)]))

;; ---------------------------------
;; case-> and Ccase->

;; Ccase-> must check that its subparts are concrete function types
(define-syntax Ccase->
  (syntax-parser
    [(_ . tys)
     #:do [(define (concrete-function-type? τ)
             (or (C→/normal? τ) (C→*/internal? τ)))]
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap concrete-function-type? #'tys+)
                   "Ccase-> require concrete function types"
     #'(Ccase->* . tys+)]))


;; TODO: What should case-> do when given symbolic function
;; types? Should it transform (case-> (U (C→ τ ...)) ...)
;; into (U (Ccase-> (C→ τ ...) ...)) ? What makes sense here?

;; ---------------------------------
;; Symbolic versions of types

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

(define-named-type-alias NegInt (add-predm (U CNegInt) negative-integer?))
(define-named-type-alias Zero (add-predm (U CZero) zero-integer?))
(define-named-type-alias PosInt (add-predm (U CPosInt) positive-integer?))
(define-named-type-alias Float (U CFloat))
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
     (add-pred
      (add-orig 
       #'(U (C→ ty ...)) 
       this-syntax)
      #'ro:fv?)]))

(define-syntax define-symbolic-named-type-alias
  (syntax-parser
    [(_ Name:id Cτ:expr #:pred p?)
     #:with Cτ+ ((current-type-eval) #'Cτ)
     #:fail-when (and (not (concrete? #'Cτ+)) #'Cτ+)
                 "should be a concrete type"
     #:with CName (format-id #'Name "C~a" #'Name #:source #'Name)
     #'(begin-
         (define-named-type-alias CName Cτ)
         (define-named-type-alias Name (add-predm (U CName) p?)))]))

(define-symbolic-named-type-alias Bool (CU CFalse CTrue) #:pred ro:boolean?)
(define-symbolic-named-type-alias Nat (CU CZero CPosInt) #:pred nonnegative-integer?)

(define-symbolic-named-type-alias Int (CU CNegInt CNat) #:pred ro:integer?)
(define-symbolic-named-type-alias Num (CU CFloat CInt) #:pred ro:real?)

(define-named-type-alias BV (add-predm (U CBV) ro:bv?))

(define-named-type-alias CAsserts (CListof Bool))

;; ---------------------------------------------------------

(define-type-constructor CSequenceof #:arity = 1)
(define-type-constructor CStructTypeProp #:arity = 1)

(begin-for-syntax
  (begin-for-syntax
    (define-syntax-class expr*
      [pattern (~and :expr (~not [:keyword . _]))]))
  (define-syntax-class expr*
    [pattern (~and :expr (~not [:keyword . _]))]))

;; ---------------------------------------------------------

;; Function Types

(begin-for-syntax
  (define (C→? τ)
    (C→*/internal? τ))
  (define (concrete-function-type? τ)
    (or (C→? τ) (Ccase->? τ))))

(define-internal-type-constructor C→*/internal) ; #:arity = 4
(define-internal-type-constructor MandArgs) ; #:arity >= 0
(define-internal-type-constructor OptKws) ; #:arity >= 1

(define-internal-type-constructor NoRestArg) ; #:arity = 0
(define-internal-type-constructor RestArg) ; #:arity = 1

(define-internal-type-constructor KwArg) ; #:arity = 2

;; (C→* mandatory-args optional-kws output)
;; (C→* mandatory-args optional-kws #:rest rest output)
;;   mandatory-args ::= [τ ...]
;;     optional-kws ::= [[kw τ] ...]
;;             rest ::= τ
;;           output ::= τ
(define-typed-syntax C→*
  [(_ [τ_in:expr* ...] [[kw:keyword τ_kw:expr*] ...] τ_out:expr*) ≫
   [⊢ [τ_in ≫ τ_in- ⇐ :: #%type] ...]
   [⊢ [τ_kw ≫ τ_kw- ⇐ :: #%type] ...]
   [⊢ τ_out ≫ τ_out- ⇐ :: #%type]
   --------
   [⊢ (C→*/internal- (MandArgs- τ_in- ...)
                     (OptKws- (KwArg- (quote-syntax kw) τ_kw-) ...)
                     (NoRestArg-)
                     τ_out-)
      ⇒ :: #%type]]
  [(_ #:rest τ_rst τ_out:expr*) ≫
   --------
   [≻ (C→* [] [] #:rest τ_rst τ_out)]]
  [(_ [τ_in:expr* ...] [[kw:keyword τ_kw:expr*] ...] #:rest τ_rst τ_out:expr*) ≫
   [⊢ [τ_in ≫ τ_in- ⇐ :: #%type] ...]
   [⊢ [τ_kw ≫ τ_kw- ⇐ :: #%type] ...]
   [⊢ τ_rst ≫ τ_rst- ⇐ :: #%type]
   [⊢ τ_out ≫ τ_out- ⇐ :: #%type]
   --------
   [⊢ (C→*/internal- (MandArgs- τ_in- ...)
                     (OptKws- (KwArg- (quote-syntax kw) τ_kw-) ...)
                     (RestArg- τ_rst-)
                     τ_out-)
      ⇒ :: #%type]])

(define-typed-syntax C→
  [(_ τ_in:expr* ... [kw:keyword τ_kw:expr*] ... τ_out:expr*) ≫
   --------
   [≻ (C→* [τ_in ...] [[kw τ_kw] ...] τ_out)]])

(begin-for-syntax
  (define (convert-opt-kws opt-kws)
    (syntax-parse opt-kws
      [(~OptKws (~KwArg ((~literal quote-syntax) kw) τ) ...)
       #'[[kw τ] ...]]))
  (define-syntax ~C→*
    (pattern-expander
     (syntax-parser
       [(_ [pat_in:expr* ...] [pat_kw:expr ...] pat_out:expr*)
        #:with opt-kws (generate-temporary 'opt-kws)
        #'(~C→*/internal
           (~MandArgs pat_in ...)
           (~and opt-kws
                 (~parse [pat_kw ...] (convert-opt-kws #'opt-kws)))
           (~NoRestArg)
           pat_out)]
       [(_ [pat_in:expr* ...] [pat_kw:expr ...] #:rest pat_rst:expr pat_out:expr*)
        #:with opt-kws (generate-temporary 'opt-kws)
        #'(~C→*/internal
           (~MandArgs pat_in ...)
           (~and opt-kws
                 (~parse [pat_kw ...] (convert-opt-kws #'opt-kws)))
           (~RestArg pat_rst)
           pat_out)]))))

(begin-for-syntax
  (define-syntax ~C→
    (pattern-expander
     (syntax-parser
       [(_ pat_in:expr* ... (~and pat_out:expr* (~not (~literal ...))))
        #'(~C→* [pat_in ...] [] pat_out)]))))


;; ---------------------------------------------------------

;; Extra convenience types for predicates

(define-named-type-alias LiftedPred (Ccase-> (C→ CAny CBool)
                                             (C→ Any Bool)))
(define-named-type-alias LiftedPred2 (Ccase-> (C→ CAny CAny CBool)
                                              (C→ Any Any Bool)))
(define-named-type-alias LiftedNumPred (Ccase-> (C→ CNum CBool)
                                                (C→ Num Bool)))
(define-named-type-alias LiftedIntPred (Ccase-> (C→ CInt CBool)
                                                (C→ Int Bool)))
(define-named-type-alias UnliftedPred (C→ Any CBool))

(define-symbolic-named-type-alias BVPred LiftedPred
  #:pred lifted-bitvector?)

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
     (and (concrete/recur? t1) (CAny? t2))
     ((current-type=?) t1 t2)
     (syntax-parse (list t1 t2)
       ;; Constant clause must appear before U, ow (Const Int) <: Int wont hold
       [((~Constant* ty1) (~Constant* ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~Constant* ty) _) 
        (typecheck? #'ty t2)]
       [((~CListof ty1) (~CListof ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CList . tys1) (~CList . tys2))
        (and (stx-length=? #'tys1 #'tys2)
             (typechecks? #'tys1 #'tys2))]
       [((~CList . tys) (~CListof ty))
        (for/and ([t (stx->list #'tys)])
          (typecheck? t #'ty))]
       ;; vectors, only immutable vectors are invariant
       [((~CIVectorof ty1) (~CIVectorof ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CIBoxof ty1) (~CIBoxof ty2))
        (typecheck? #'ty1 #'ty2)]
       [((~CPair ty1a ty1b) (~CPair ty2a ty2b))
        (and (typecheck? #'ty1a #'ty2a)
             (typecheck? #'ty1b #'ty2b))]
       ; 2 U types, subtype = subset
       [((~CU* . ts1) _)
        (for/and ([t (stx->list #'ts1)])
          (typecheck? t t2))]
       [((~U* . ts1) _)
        (and
         (not (concrete? t2))
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
       [((~C→ s1 ... s2) (~C→ t1 ... t2))
        (and (typechecks? #'(t1 ...) #'(s1 ...))
             (typecheck? #'s2 #'t2))]
       [_ #f])))
  (current-sub? sub?)
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2))))

