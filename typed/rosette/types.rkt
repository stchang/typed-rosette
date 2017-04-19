#lang turnstile

(provide CAny Any
         CNothing Nothing
         Term
         CU U
         Constant
         (for-syntax Any?
                     ~Term*
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
         CBoxof CMBoxof CIBoxof MBoxof  IBoxof
         CVectorof CMVectorof CIVectorof CVector
         Vectorof MVectorof IVectorof
         (for-syntax ~CHashTable
                     ~CSequenceof
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
         (for-syntax get-pred
                     type-merge
                     type-merge*
                     typeCFalse
                     typeCTrue))

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
  )

;; TODO: update orig to use reduced type
(define-syntax (CU stx)
  (syntax-parse stx
    [(_ . tys)
     #:with tys+ (stx-map (current-type-eval) #'tys)
     #:fail-unless (stx-andmap concrete? #'tys+)
                   "CU requires concrete types"
     #'(CU* . tys+)]))

;; user-facing symbolic U constructor: flattens and prunes
(define-syntax (U stx)
  (syntax-parse stx
    [(_ . tys)
     ;; canonicalize by expanding to U*, with only (sorted and pruned) leaf tys
     #:with ((~or (~U* ty1- ...) (~CU* ty2- ...) ty3-) ...) (stx-map (current-type-eval) #'tys)
     #:with tys- (prune+sort #'(ty1- ... ... ty2- ... ... ty3- ...))
     #'(U* . tys-)]))

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
     #'(Constant* τ.norm)]))

;; ---------------------------------

(define-base-types
  CAny Any CBV CStx CSymbol CRegexp
  CSolution CSolver CPict
  COutputPort)

;; CVectorof includes all vectors
;; CIVectorof includes only immutable vectors
;; CMVectorof includes only mutable vectors
(define-type-constructor CIVectorof #:arity = 1)
(define-type-constructor CIBoxof #:arity = 1)
(define-internal-type-constructor CMVectorof) ; #:arity = 1
(define-internal-type-constructor CMBoxof) ; #:arity = 1

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

;; ---------------------------------
;; Pattern Expanders for Types

(define-internal-type-constructor C→*/internal) ; #:arity = 4
(define-internal-type-constructor MandArgs) ; #:arity >= 0
(define-internal-type-constructor OptKws) ; #:arity >= 1

(define-internal-type-constructor NoRestArg) ; #:arity = 0
(define-internal-type-constructor RestArg) ; #:arity = 1

(define-internal-type-constructor KwArg) ; #:arity = 2

(begin-for-syntax
  (begin-for-syntax
    (define-syntax-class expr*
      [pattern (~and :expr (~not [:keyword . _]))]))
  (define-syntax-class expr*
    [pattern (~and :expr (~not [:keyword . _]))])

  (define-syntax ~C→
    (pattern-expander
     (syntax-parser
       [(_ pat_in:expr* ... (~and pat_out:expr* (~not (~literal ...))))
        #'(~C→* [pat_in ...] [] pat_out)])))

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
           pat_out)])))
  )

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

(define-named-type-alias CBool (CU CFalse CTrue))

(define-named-type-alias CNat (CU CZero CPosInt))
(define-named-type-alias CInt (CU CNegInt CNat))
(define-named-type-alias CNum (CU CFloat CInt))

(begin-for-syntax
  (define (concrete-type-solvable? τ)
    (or (concrete-type-solvable-base? τ)
        (syntax-parse τ
          [(~C→ (~and (~or (~U* τ_in) τ_in))
                ...
                (~or (~U* τ_out) τ_out))
           (stx-andmap type-solvable? #'[τ_in ... τ_out])]
          [_ #false])))

  (define typeCFalse ((current-type-eval) #'CFalse))
  (define typeCTrue ((current-type-eval) #'CTrue))
  (define typeCBool ((current-type-eval) #'CBool))
  (define typeCInt ((current-type-eval) #'CInt))
  (define typeCNum ((current-type-eval) #'CNum))
  (define typeCBV ((current-type-eval) #'CBV))

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

(define-named-type-alias True (U (Term CTrue)))
(define-named-type-alias False (U (Term CFalse)))
(define-named-type-alias Bool (add-predm (U (Term CBool)) ro:boolean?))
(define-named-type-alias Nat (add-predm (U (Term CNat)) nonnegative-integer?))

(define-named-type-alias Int (add-predm (U (Term CInt)) ro:integer?))
(define-named-type-alias Num (add-predm (U (Term CNum)) ro:real?))

(define-named-type-alias BV (add-predm (U (Term CBV)) ro:bv?))

(define-named-type-alias CAsserts (CListof Bool))

;; ---------------------------------------------------------

(define-type-constructor CSequenceof #:arity = 1)
(define-type-constructor CStructTypeProp #:arity = 1)

;; ---------------------------------------------------------

;; Function Types

(begin-for-syntax
  (define (C→? τ)
    (C→*/internal? τ))
  (define (concrete-function-type? τ)
    (or (C→? τ) (Ccase->? τ))))

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

(define-named-type-alias CBVPred LiftedPred)
(define-named-type-alias BVPred (add-predm (U LiftedPred) lifted-bitvector?))

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
;; All *base* single-shape types must be solvable
;;   μ(u, v) :=
;;     / (Term (CU u v))     if sameBaseSingleShape(u, v)
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
  (define (type-merge a* b*)
    (define a (syntax-parse a* [(~Constant* a) #'a] [_ a*]))
    (define b (syntax-parse b* [(~Constant* b) #'b] [_ b*]))
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
        (type-merge/single-shape-solvable a b)))
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
       [((~C→ s1 ... s2) (~C→ t1 ... t2))
        (and (typechecks? #'(t1 ...) #'(s1 ...))
             (typecheck? #'s2 #'t2))]
       [_ #f])))
  (current-sub? sub?)
  (current-typecheck-relation sub?)
  (define (subs? τs1 τs2)
    (and (stx-length=? τs1 τs2)
         (stx-andmap (current-sub?) τs1 τs2))))

