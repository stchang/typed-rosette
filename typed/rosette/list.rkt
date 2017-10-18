#lang turnstile

(provide cons pair car cdr null
         length list-ref first rest second
         map filter foldl for-each member? remove-duplicates
         cartesian-product* append* append sort
         andmap ormap
         build-list make-list range splitf-at)

(require (rename-in typed/rosette/base-forms [#%app tro:#%app])
         typed/rosette/types
         typed/rosette/bool
         typed/rosette/forms-pre-match
         typed/rosette/unsafe
         (only-in turnstile/examples/stlc+tup
                  tup proj)
         (prefix-in ro: rosette))

;; ----------------------------------------------------------------------------

;; Basic list and pair stuff

(provide (typed-out [null? : (Ccase-> (C→ (CListof Any) CBool)
                                      (C→ (Listof Any) Bool))]
                    [empty? : (Ccase-> (C→ (CListof Any) CBool)
                                       (C→ (Listof Any) Bool))]
                    [list? : LiftedPred]))

(define-typed-syntax null
  [(_ {τ}) ≫
   --------
   [⊢ ro:null ⇒ (CListof τ)]])

(define-typed-syntax cons
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:cons ⇒ : (Ccase-> 
                        (C→ Any Any (CPair Any Any))
                        (C→ Any (CListof Any) (CListof Any))
                        (C→ Any (Listof Any) (Listof Any)))]]]
  [(_ e1:expr e2:expr) ≫
   [⊢ [e2 ≫ e2- ⇒ : (~CListof τ1)]]
   [⊢ [e1 ≫ e1- ⇒ : τ2]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) 
           ⇒ : #,(if (and (concrete? #'τ1) (concrete? #'τ2))
                     #'(CListof (CU τ1 τ2))
                     #'(CListof (U τ1 τ2)))]]]
  [(_ e1:expr e2:expr) ≫
   [⊢ [e2 ≫ e2- ⇒ : (~U* (~CListof τ) ...)]]
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (U (CListof (U τ1 τ)) ...)]]]
  [(_ e1:expr e2:expr) ≫
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : (~CList τ ...)]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (CList τ1 τ ...)]]]
  [(_ e1:expr e2:expr) ≫
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : (~U* (~CList τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (U (CList τ1 τ ...) ...)]]]
  [(_ e1:expr e2:expr) ≫
   [⊢ [e1 ≫ e1- ⇒ : τ1]]
   [⊢ [e2 ≫ e2- ⇒ : τ2]]
   --------
   [⊢ [_ ≫ (ro:cons e1- e2-) ⇒ : (CPair τ1 τ2)]]])

(define-typed-syntax pair
  [(_ e1:expr e2:expr) ≫
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

;; ------------------------------------------------------------------------

;; Lists

(define-typed-syntax length
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:length ⇒ : (Ccase-> (C→ (CListof Any) CNat)
                                  (C→ (Listof Any) Nat))]]]
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof _)]
   --------
   [⊢ (ro:length lst-) ⇒ CNat]]
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~U* (~CListof _) ...)]
   --------
   [⊢ (ro:length lst-) ⇒ Nat]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~CList _ ...)]]
   --------
   [⊢ [_ ≫ (ro:length lst-) ⇒ : CNat]]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~U* (~CList _ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:length lst-) ⇒ : Nat]]])

(define-typed-syntax list-ref
  [(_ lst:expr i:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof τ)]
   [⊢ i ≫ i- ⇐ CNat]
   --------
   [⊢ (ro:list-ref lst- i-) ⇒ τ]]
  [(_ lst:expr i:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~or (~CListof τ)
                        (~U* (~CListof τ)))]
   [⊢ i ≫ i- ⇐ Nat]
   --------
   [⊢ (ro:list-ref lst- i-) ⇒ (U τ)]])

(define-typed-syntax first
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:first ⇒ : (C→ (Listof Any) Any)]]]
  [(_ lst) ≫
   [⊢ [lst ≫ lst- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:first lst-) ⇒ : τ]]]
  [(_ lst) ≫
   [⊢ [lst ≫ lst- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:first lst-) ⇒ : (U τ ...)]]]
  [(_ lst) ≫
   [⊢ [lst ≫ lst- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:first lst-) ⇒ : τ1]]]
  [(_ lst) ≫
   [⊢ [lst ≫ lst- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:first lst-) ⇒ : (U τ1 ...)]]])

(define-typed-syntax rest
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:rest ⇒ : (Ccase-> (C→ (CListof Any) (CListof Any))
                                (C→ (Listof Any) (Listof Any)))]]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:rest lst-) ⇒ : (CListof τ)]]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:rest lst-) ⇒ : (U (CListof τ) ...)]]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~CList τ1 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:rest lst-) ⇒ : (CList τ ...)]]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~U* (~CList τ1 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:rest lst-) ⇒ : (U (CList τ ...) ...)]]])

(define-typed-syntax second
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:second ⇒ : (C→ (Listof Any) Any)]]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~CListof τ)]]
   --------
   [⊢ [_ ≫ (ro:second lst-) ⇒ : τ]]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~U* (~CListof τ) ...)]]
   --------
   [⊢ [_ ≫ (ro:second lst-) ⇒ : (U τ ...)]]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~CList τ1 τ2 τ ...)]]
   --------
   [⊢ [_ ≫ (ro:second lst-) ⇒ : τ2]]]
  [(_ lst:expr) ≫
   [⊢ [lst ≫ lst- ⇒ : (~U* (~CList τ1 τ2 τ ...) ...)]]
   --------
   [⊢ [_ ≫ (ro:second lst-) ⇒ : (U τ2 ...)]]])

;; ------------------------------------------------------------------------

(define-typed-syntax map
  #;[_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:map ⇒ : (C→ (C→ Any Any) (CListof Any) (CListof Any))]]]
  [(_ f:expr lst:expr) ⇐ (~CListof Y) ≫
   [⊢ f ≫ f- ⇒ (~C→ X ... Y*)]
   ; Y* must be usable as Y, because the Y* value will be used
   ; as an element the return value
   [Y* τ⊑ Y #:for f]
   [⊢ lst ≫ lst- ⇐ (CListof X)] ...
   --------
   [⊢ (ro:map f- lst- ...)]]
  [(_ f:expr lst:expr ...) ≫
   [⊢ [f ≫ f- ⇒ : (~C→ ~! X ... Y)]]
   [⊢ [lst ≫ lst- ⇐ : (CListof X)] ...]
   --------
   [⊢ [_ ≫ (ro:map f- lst- ...) ⇒ : (CListof Y)]]]
  [(_ f:expr lst:expr ...) ≫
   [⊢ [lst ≫ lst- ⇒ : (~CListof X)] ...]
   [⊢ [f ≫ f- ⇒ : (~Ccase-> ~! ty-fns ...)]] ; find first match
   #:with (~C→ _ ... Y)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ X* ... _) #:when (typechecks? #'(X ...) #'(X* ...)) #t]
                               [_ #f]))
            ty-fn)
   --------
   [⊢ [_ ≫ (ro:map f- lst- ...) ⇒ : (CListof Y)]]]
  [(_ f:expr lst:expr ...) ≫
   [⊢ [lst ≫ lst- ⇒ : (~U* (~CListof X))] ...]
   [⊢ [f ≫ f- ⇒ : (~Ccase-> ~! ty-fns ...)]] ; find first match
   #:with (~C→ _  ... Y)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ X* ... _) #:when (typecheck? #'(X ...) #'(X* ...)) #t]
                               [_ #f]))
            ty-fn)
   --------
   [⊢ [_ ≫ (ro:map f- lst- ...) ⇒ : (CListof Y)]]])

(define-typed-syntax filter
  [(_ f:expr lst:expr) ≫
   [⊢ [f ≫ f- ⇒ : (~C→ ~! X Bool)]]
   [⊢ [lst ≫ lst- ⇐ (CListof X)]]
   --------
   [⊢ [_ ≫ (ro:filter f- lst-) ⇒ : (CListof X)]]])

(define-typed-syntax for-each
  [(_ f lst ...) ≫
   [⊢ f ≫ f- ⇒ (~C→ ty1 ... _)]
   [⊢ lst ≫ lst- ⇐ (CListof ty1)] ...
   --------
   [⊢ (ro:for-each f- lst- ...) ⇒ CUnit]]
  [(_ f lst ...) ≫
   [⊢ f ≫ f- ⇒ (~C→ ~! ty1 ... _)]
   [⊢ lst ≫ lst- ⇐ (Listof ty1)] ...
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

(define-typed-syntax foldl
  [(_ f:expr base:expr lst:expr) ⇐ Y ≫
   [⊢ f ≫ f- ⇒ (~C→ X Y* Z)]
   ; Z must be usable as Y*, because the Z value will be
   ; used as the Y* argument on the next iteration
   [Z τ⊑ Y* #:for f]
   ; Z must be usable as Y, because the Z value will be used
   ; as the return value
   [Z τ⊑ Y #:for f]
   ; Y must be usable as Y*, because the base Y value will
   ; be used as the Y* argument on the first iteration
   [Y τ⊑ Y* #:for f]
   ; base must be usable as Y, because the base value will
   ; be used as the return value
   [⊢ base ≫ base- ⇐ Y]
   [⊢ lst ≫ lst- ⇐ (CListof X)]
   --------
   [⊢ (ro:foldl f- base- lst-)]]
  [(_ f:expr base:expr lst:expr) ⇐ Y ≫
   ; TODO: fix this to take X into account when choosing
   ; which case to commit to
   [⊢ f ≫ f- ⇒
      (~Ccase-> _ ...
                (~and (~C→ X Y* Z)
                      (~fail #:unless (typecheck? #'Z #'Y*))
                      (~fail #:unless (typecheck? #'Z #'Y))
                      (~fail #:unless (typecheck? #'Y #'Y*)))
                _ ...)]
   ; base must be usable as Y, because the base value will
   ; be used as the return value
   [⊢ base ≫ base- ⇐ Y]
   [⊢ lst ≫ lst- ⇐ (CListof X)]
   --------
   [⊢ (ro:foldl f- base- lst-)]]
  [(_ f:expr base:expr lst:expr) ≫
   ; TODO: fix this to try all options in the Ccase->
   [⊢ f ≫ f- ⇒ (~Ccase-> _ ... (~C→ X Y Z))]
   ; Z must be usable as Y, because the Z value will be used
   ; as the Y argument on the next iteration
   [Z τ⊑ Y #:for f]
   [⊢ base ≫ base- ⇐ Y]
   [⊢ lst ≫ lst- ⇐ (CListof X)]
   --------
   [⊢ (ro:foldl f- base- lst-) ⇒ Y]])

(define-typed-syntax remove-duplicates
  [(_ lst) ≫
   [⊢ lst ≫ lst- (⇐ (Listof Any)) (⇒ ty-out)]
   --------
   [⊢ (ro:remove-duplicates lst-) ⇒ ty-out]])

(define member
  (unsafe-assign-type ro:member :
                      (C→ Any (Listof Any) Any)))

(: member? : (C→ Any (Listof Any) Bool))
(define (member? v lov)
  (if (tro:#%app member v lov) '#true '#false))

(define-typed-syntax cartesian-product*
  [(_ lst:expr) ≫
   [⊢ lst ≫ lst- ⇒ (~CListof (~CListof τ))]
   --------
   [⊢ (ro:apply ro:cartesian-product lst-)]])

(define-typed-syntax append
  [(_ l0 l:expr ...) ≫
   [⊢ l0 ≫ l0- ⇒ (~CListof τ)]
   [⊢ l ≫ l- ⇐ (CListof τ)] ...
   --------
   [⊢ (ro:append l0 l- ...) ⇒ (CListof τ)]])

(define-typed-syntax append*
  [(_ lol:expr) ≫
   [⊢ lol ≫ lol- ⇒ (~CListof (~CListof τ))]
   --------
   [⊢ (ro:append* lol-) ⇒ (CListof τ)]])

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

;; ------------------------------------------------------------------------

;; TODO: finish andmap and ormap
(define-typed-syntax andmap
  #;[_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ [_ ≫ ro:andmap ⇒ : (C→ (C→ Any Bool) (CListof Any) Bool)]]]
  [(_ f lst) ≫
   [⊢ [f ≫ f- ⇒ : (~C→ ~! ty ty-bool : #:+ p+ #:- _)]]
   [⊢ [lst ≫ lst- ⇒ : (~CListof _)]]
   #:with prop_out+
   (syntax-parse #'p+
     [(~Prop/IndexType (_ 0) τ_elem)
      #`(Prop/ObjType #,(get-arg-obj #'lst-) : (CListof τ_elem))]
     [_ #`Prop/Top])
   --------
   [⊢ [_ ≫ (ro:andmap f- lst-) (⇒ : Bool) (⇒ prop+ prop_out+)]]]
  #;[(_ f lst) ≫
   [⊢ [lst ≫ lst- ⇒ : (~CListof ty)]]
   [⊢ [f ≫ f- ⇒ : (~Ccase-> ~! ty-fns ...)]] ; find first match
   #:with (~C→ _ ty2)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ t1 _) #:when (typecheck? #'ty1 #'t1) #t]
                               [_ #f]))
            (displayln (syntax->datum ty-fn))
            ty-fn)
   --------
   [⊢ [_ ≫ (ro:andmap f- lst-) ⇒ : (CListof ty2)]]]
  #;[(_ f lst) ≫
   [⊢ [lst ≫ lst- ⇒ : (~U* (~CListof ty1))]]
   [⊢ [f ≫ f- ⇒ : (~Ccase-> ~! ty-fns ...)]] ; find first match
   #:with (~C→ _ ty2)
          (for/first ([ty-fn (stx->list #'(ty-fns ...))]
                      #:when (syntax-parse ty-fn
                               [(~C→ t1 _) #:when (typecheck? #'ty1 #'t1) #t]
                               [_ #f]))
            ty-fn)
   --------
   [⊢ [_ ≫ (ro:andmap f- lst-) ⇒ : (CListof ty2)]]])

(define-typed-syntax ormap
  [(_ f lst) ≫
   [⊢ [f ≫ f- ⇒ : (~C→ ~! ty ty-bool : #:+ p+ #:- _)]]
   [⊢ [lst ≫ lst- ⇐ : (CListof ty)]]
   #:with prop_out+
   (syntax-parse #'p+
     [(~Prop/IndexType (_ 0) τ_elem)
      #`(Prop/ObjType #,(get-arg-obj #'lst-) : (CListof τ_elem))]
     [_ #`Prop/Top])
   --------
   [⊢ [_ ≫ (ro:ormap f- lst-) (⇒ : ty-bool) (⇒ prop+ prop_out+)]]])


;; ----------------------------------------------------------------------------
;; not rosette/safe

(define-typed-syntax build-list
  [_:id ≫ ;; TODO: use polymorphism
   --------
   [⊢ ro:build-list ⇒ : (C→ CNat (C→ CNat Any) (CListof Any))]]
  [(_ n:expr f:expr) ≫
   [⊢ n ≫ n- ⇐ : CInt]
   [⊢ f ≫ f- ⇒ : (~C→ X Y)]
   #:fail-unless (typecheck? #'X ((current-type-eval) #'CInt))
                 "expected function that consumes concrete Int"
   --------
   [⊢ [_ ≫ (ro:build-list n- f-) ⇒ : (CListof Y)]]])

(define-typed-syntax make-list
  [(_ n:expr v:expr) ≫
   [⊢ n ≫ n- ⇐ : CNat]
   [⊢ v ≫ v- ⇒ : τ]
   --------
   [⊢ (ro:make-list n- v-) ⇒ : (CListof τ)]])

(define-typed-syntax range
  [(_ n:expr) ≫
   [⊢ n ≫ n- ⇐ CNat]
   ------------------
   [⊢ (ro:range n-) ⇒ (CListof CNat)]])

(define-typed-syntax splitf-at
  [(_ l f) ≫
   [⊢ l ≫ l- ⇒ (~CListof τ)]
   [⊢ f ≫ f- ⇐ (C→ τ CAny)]
   -----------
   [⊢ (ro:let-values ([(l r) (ro:splitf-at l- f-)]) (ro:list l r))
      ⇒ (CList (CListof τ) (CListof τ))]])
