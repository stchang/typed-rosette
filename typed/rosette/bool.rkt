#lang turnstile

(require typed/rosette/types
         (only-in typed/rosette/base-forms begin unsafe-assign-type)
         (prefix-in ro: rosette)
         (postfix-in - rosette))

;; ---------------------------------

;; if

(provide if)

;; TODO: this is not precise enough
;; specifically, a symbolic non-bool should produce a concrete val
(define-typed-syntax if
  [(_ e_tst e1 e2) ≫
   [⊢ [e_tst ≫ e_tst-
             (⇒ : ty_tst)
             (⇒ prop+ posprop)
             (⇒ prop- negprop)]]
   #:when (or (concrete? #'ty_tst) ; either concrete
              ; or non-bool symbolic
              ; (not a super-type of CFalse)
              (and (not (typecheck? ((current-type-eval) #'CFalse) #'ty_tst))
                   (not (typecheck? ((current-type-eval) #'(Constant (Term CFalse))) #'ty_tst))))
   [⊢ [(with-occurrence-prop posprop e1) ≫ e1- ⇒ : ty1]]
   [⊢ [(with-occurrence-prop negprop e2) ≫ e2- ⇒ : ty2]]
   #:with τ_out
   (cond [(and (concrete? #'ty1) (concrete? #'ty2)) #'(CU ty1 ty2)]
         [(typecheck? #'ty1 typeCNothing) #'ty2]
         [(typecheck? #'ty2 typeCNothing) #'ty1]
         ;; else don't need to merge, but do need U
         [else #'(U ty1 ty2)])
   --------
   [⊢ [_ ≫ (ro:if e_tst-
                  e1-
                  e2-)
         ⇒ : τ_out]]]
  [(_ e_tst e1 e2) ≫
   [⊢ [e_tst ≫ e_tst-
             (⇒ : _)
             (⇒ prop+ posprop)
             (⇒ prop- negprop)]]
   [⊢ [(with-occurrence-prop posprop e1) ≫ e1- ⇒ : ty1]]
   [⊢ [(with-occurrence-prop negprop e2) ≫ e2- ⇒ : ty2]]
   #:with τ_out (type-merge #'ty1 #'ty2)
   --------
   [⊢ [_ ≫ (ro:if e_tst- e1- e2-) ⇒ : τ_out]]])

;; ----------------------------------------------------------------------------

;; Other Conditionals

(provide when unless cond else)

(define-typed-syntax when
  [(_ condition:expr body:expr ...+) ≫
   [⊢ condition ≫ condition- (⇐ : Bool) (⇒ prop+ posprop)]
   [⊢ (with-occurrence-prop posprop (begin body ...)) ≫ body- ⇒ τ]
   --------
   [⊢ (ro:when condition- body-) ⇒ (U τ Void)]])

(define-typed-syntax unless
  [(_ condition:expr body:expr ...+) ≫
   [⊢ condition ≫ condition- (⇐ : Bool) (⇒ prop- negprop)]
   [⊢ (with-occurrence-prop negprop (begin body ...)) ≫ body- ⇒ τ]
   --------
   [⊢ (ro:unless condition- body-) ⇒ (U τ Void)]])

(define-syntax-parser cond
  #:literals [else]
  [(_ [else ~! body:expr])
   #'body]
  [(_ [(~and b:expr (~not else)) ~! v:expr] rst ... [else body:expr])
   (quasisyntax/loc this-syntax
     (if b
         v
         #,(syntax/loc this-syntax (cond rst ... [else body]))))])

;; ------------------------------------------------------------------------

;; and, or, not

(provide and or not)

(define-typed-syntax and
  [(_) ≫
   --------
   [⊢ (ro:and)
      (⇒ : CTrue)
      (⇒ prop+ Prop/Top)
      (⇒ prop- Prop/Bot)]]
  [(_ e:expr) ≫
   [⊢ e ≫ e- (⇒ : τ) (⇒ prop+ p+) (⇒ prop- p-)]
   --------
   [⊢ e- (⇒ : τ) (⇒ prop+ (Prop p+)) (⇒ prop- (Prop p-))]]
  [(_ e:expr ... e_l:expr) ≫
   [⊢ (and e ...) ≫ e- (⇒ : τ) (⇒ prop+ p+) (⇒ prop- p-)]
   [⊢ (with-occurrence-prop p+ e_l) ≫ e_l-
      (⇒ : τ_l)
      (⇒ prop+ pl+)
      (⇒ prop- pl-)]
   #:with τ_out (cond [(and (concrete? #'τ) (concrete? #'τ_l))
                       #'(CU CFalse τ_l)]
                      [(concrete? #'τ)
                       #'(U CFalse τ_l)]
                      [else
                       (type-merge typeCFalse #'τ_l)])
   --------
   [⊢ (ro:and e- e_l-)
      (⇒ : τ_out)
      (⇒ prop+ (Prop/And (Prop p+) (Prop pl+)))
      (⇒ prop- (Prop/Or (Prop p-) (Prop pl-)))]])

(define-typed-syntax or
  [(_) ≫
   --------
   [⊢ [_ ≫ (ro:or)
         (⇒ : CFalse)
         (⇒ prop+ Prop/Bot)
         (⇒ prop- Prop/Top)]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- (⇐ : CBool) (⇒ prop+ p+) (⇒ prop- p-)]
      ...]
   --------
   [⊢ [_ ≫ (ro:or e- ...)
         (⇒ : CBool)
         (⇒ prop+ (Prop/Or p+ ...))
         (⇒ prop- (Prop/And p- ...))]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- (⇐ : Bool) (⇒ prop+ p+) (⇒ prop- p-)]
      ...]
   --------
   [⊢ [_ ≫ (ro:or e- ...)
         (⇒ : Bool)
         (⇒ prop+ (Prop/Or p+ ...))
         (⇒ prop- (Prop/And p- ...))]]]
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : ty] ...]
   --------
   [⊢ [_ ≫ (ro:or e- ...) ⇒ : #,(type-merge* (cons typeCFalse #'[ty ...]))]]])

(define-typed-syntax not
  [:id ≫
   --------
   [⊢ ro:not ⇒ (LiftedPredFor False)]]
  [(_ e) ≫
   [⊢ e ≫ e- (⇒ : τ) (⇒ prop+ p+) (⇒ prop- p-)]
   #:when (concrete? #'τ)
   --------
   [⊢ [_ ≫ (ro:not e-) (⇒ : CBool) (⇒ prop+ (Prop p-)) (⇒ prop- (Prop p+))]]]
  [(_ e) ≫
   [⊢ e ≫ e- (⇒ : _) (⇒ prop+ p+) (⇒ prop- p-)]
   --------
   [⊢ [_ ≫ (ro:not e-) (⇒ : Bool) (⇒ prop+ (Prop p-)) (⇒ prop- (Prop p+))]]])

;; ----------------------------------------------------------------------------

;; Bool Functions

(provide (typed-out [xor : (Ccase-> (C→ CAny CAny CAny)
                                    (C→ Any Any Any))]
                    [false? : (LiftedPredFor False)]
                    
                    [true : CTrue]
                    [false : CFalse]
                    ))

;; ----------------------------------------------------------------------------

