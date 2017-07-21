#lang turnstile

(provide : define define/conc set! λ λ/conc apply ann begin list
         let
         (rename-out [app #%app])
         (for-syntax expand/ro)
         unsafe-assign-type) ; ocelot needs this

(require (only-in turnstile/examples/stlc+union ann)
         (prefix-in ro: rosette/safe)
         "types.rkt"
         (only-in typed/rosette/unsafe unsafe-assign-type) ; ocelot needs this
         (for-syntax syntax/parse/class/local-value))

(begin-for-syntax
  ;; split-at* : [Listof A] [Listof Natural] -> [Listof [Listof A]]
  (define (split-at* lst lengths)
    (cond [(empty? lengths) (list lst)]
          [else
           (define-values [fst rst]
             (split-at lst (first lengths)))
           (cons fst (split-at* rst (rest lengths)))]))

  ;; transpose : [StxListof [StxListof A]] -> [StxListof [StxListof A]]
  (define (transpose lol)
    (apply stx-map list (stx->list lol)))

  (define ((equal?? a) b) (equal? a b))
  (define (all-equal? lst)
    (or (empty? lst) (andmap (equal?? (first lst)) (rest lst))))

  ;; C→-arity-is? : Nat [Listof Kw] Bool -> [Type -> Bool]
  (define ((C→-arity-is? num-args kws rest?) τ)
    (syntax-parse τ
      [(~C→* [τ_in ...] [[kw τ_kw] ...] τ_out)
       (and (not rest?)
            (= num-args (stx-length #'[τ_in ...]))
            (equal? kws (syntax->datum #'[kw ...])))]
      [(~C→** [τ_in ...] [[kw τ_kw] ...] τ_out)
       (and (not rest?)
            (= num-args (stx-length #'[τ_in ...]))
            (equal? kws (syntax->datum #'[kw ...])))]
      [(~C→* [τ_in ...] [[kw τ_kw] ...] #:rest τ_rst τ_out)
       (and rest?
            (= num-args (stx-length #'[τ_in ...]))
            (equal? kws (syntax->datum #'[kw ...])))]
      [(~C→** [τ_in ...] [[kw τ_kw] ...] #:rest τ_rst τ_out)
       (and rest?
            (= num-args (stx-length #'[τ_in ...]))
            (equal? kws (syntax->datum #'[kw ...])))]))

  ;; U/preserve-concreteness : [StxListof Type] -> Type
  (define (U/preserve-concreteness τs)
    (cond [(stx-andmap concrete? τs) #`(CU #,@τs)]
          [else #`(U #,@τs)]))

  ;; C→-map-union : [StxListof Type] -> Type
  ;; DO NOT USE for soundness. Only use after you have already checked
  ;; all the cases.
  (define (C→-map-union τs)
    (syntax-parse τs
      [[(~C→* [τ_in ...] [[kw τ_kw] ...] τ_out) ...]
       #:fail-unless (all-equal? (stx-map stx-length #'[[τ_in ...] ...]))
       "function types must have the same arity"
       #:fail-unless (all-equal? (stx-map syntax->datum #'[[kw ...] ...]))
       "function types must have the same keywords"
       #:with [τ_in* ...] (stx-map U/preserve-concreteness
                                   (transpose #'[[τ_in ...] ...]))
       #:with [kw* ...] (stx-car #'[[kw ...] ...])
       #:with [τ_kw* ...] (stx-map U/preserve-concreteness
                                   (transpose #'[[τ_kw ...] ...]))
       #:with τ_out* (U/preserve-concreteness #'[τ_out ...])
       #'(C→* [τ_in* ...] [[kw* τ_kw*] ...] τ_out*)]
      [[(~C→** [τ_in ...] [[kw τ_kw] ...] τ_out) ...]
       #:fail-unless (all-equal? (stx-map stx-length #'[[τ_in ...] ...]))
       "function types must have the same arity"
       #:fail-unless (all-equal? (stx-map syntax->datum #'[[kw ...] ...]))
       "function types must have the same keywords"
       #:with [τ_in* ...] (stx-map U/preserve-concreteness
                                   (transpose #'[[τ_in ...] ...]))
       #:with [kw* ...] (stx-car #'[[kw ...] ...])
       #:with [τ_kw* ...] (stx-map U/preserve-concreteness
                                   (transpose #'[[τ_kw ...] ...]))
       #:with τ_out* (U/preserve-concreteness #'[τ_out ...])
       #'(C→** [τ_in* ...] [[kw* τ_kw*] ...] τ_out*)]
      [[(~C→* [τ_in ...] [[kw τ_kw] ...] #:rest τ_rst τ_out) ...]
       #:fail-unless (all-equal? (stx-map stx-length #'[[τ_in ...] ...]))
       "function types must have the same arity"
       #:fail-unless (all-equal? (stx-map syntax->datum #'[[kw ...] ...]))
       "function types must have the same keywords"
       #:with [τ_in* ...] (stx-map U/preserve-concreteness
                                   (transpose #'[[τ_in ...] ...]))
       #:with [kw* ...] (stx-car #'[[kw ...] ...])
       #:with [τ_kw* ...] (stx-map U/preserve-concreteness
                                   (transpose #'[[τ_kw ...] ...]))
       #:with τ_rst* (U/preserve-concreteness #'[τ_rst ...])
       #:with τ_out* (U/preserve-concreteness #'[τ_out ...])
       #'(C→* [τ_in* ...] [[kw* τ_kw*] ...] #:rest τ_rst* τ_out*)]))
  )

;; ----------------------------------------------------------------------------

;; Expanding to Rosette Forms

(begin-for-syntax
  ;; TODO: fix this so it's not using hardcoded list of ids
  (define (expand/ro e)
    (define e+
      (local-expand
       e 'expression
       (list #'ro:#%app #'ro:choose #'ro:synthesize #'ro:let #'ro:in-value
             #'ro:assert #'ro:if #'ro:? #'ro:verify)))
;    (displayln (stx->datum e+))
    e+)
  (define (mk-ro:-id id) (format-id id "ro:~a" id))
  (current-host-lang mk-ro:-id))

;; ----------------------------------------------------------------------------

;; Environments and Variables

(begin-for-syntax
  ;; var-assign/orig-binding :
  ;; Id (Listof Sym) (StxListof TypeStx) -> Stx
  (define (var-assign/orig-binding x seps τs)
    (attachs 
     (attach (attach x 'orig-binding x) 'sym-scope (current-sym-scope))
     seps
     τs
     #:ev (current-type-eval)))

  (current-var-assign var-assign/orig-binding))

;; ----------------------------------------------------------------------------

;; Declaring Types before Definitions

(begin-for-syntax
  (define (typebool->bool b)
    (syntax-parse b [~CTrue #true] [~CFalse #false]))

  (struct type-decl [internal-id internal-id-for type mutable?]
    #:property prop:procedure
    (λ (this stx)
      (match-define (type-decl x- x type mutable?) this)
      ((make-variable-like-transformer (assign-type x- type)) stx)))
  
  (define-syntax-class id/type-decl
    #:attributes [internal-id type]
    [pattern (~var x (local-value type-decl?))
      #:attr internal-id (type-decl-internal-id (attribute x.local-value))
      #:with type (type-decl-type (attribute x.local-value))])
  (define-splicing-syntax-class mut-kw
    #:attributes [mutable? mutable?/tb]
    [pattern (~seq)           #:attr mutable? #f #:attr mutable?/tb typeCFalse]
    [pattern (~seq #:mutable) #:attr mutable? #t #:attr mutable?/tb typeCTrue]))

(define-typed-syntax :
  #:datum-literals [:]
  [(_ x:id mut:mut-kw : τ:type) ≫
   #:with x- (generate-temporary #'x)
   #:fail-when (and (attribute mut.mutable?) (concrete? #'τ.norm) #'τ)
   "Mutable variables must have types that allow for symbolic values"
   #:with τ_merged (type-merge #'τ.norm #'τ.norm)
   #:fail-when (and (attribute mut.mutable?)
                    (not (typecheck? #'τ_merged #'τ.norm))
                    #'τ)
   (format (string-append
            "Mutable variable type must allow for Rosette's symbolic merging\n"
            "  merged type: ~a")
           (type->str #'τ_merged))
   #:with mutable? (attribute mut.mutable?)
   --------
   [≻ (define-syntax- x
        (type-decl #'x-
                   #'x
                   #'τ.norm
                   'mutable?))]])

;; ----------------------------------------------------------------------------

;; Define and Lambda

(begin-for-syntax
  (define-syntax-class ->
    [pattern (~or (~datum →) (~datum ->))]))

;; This new version of define handles keyword arguments,
;; and also uses make-variable-like-transformer so that
;; types are preserved accross modules.

(define-typed-syntax define
  #:datum-literals [:]
  [(_ x:id : τ e:expr) ≫
   --------
   [≻ (begin-
        (: x : τ)
        (define x e))]]
  [(_ x:id/type-decl e:expr) ≫
   #:with x- (syntax-local-introduce #'x.internal-id)
   --------
   [≻ (ro:define x- (ann e : x.type))]]
  [(_ x:id e:expr) ≫
   #:with x- (generate-temporary #'x)
   [⊢ e ≫ e- ⇒ τ]
   #:with x-/props (transfer-props #'e- (⊢ x- : τ))
   --------
   [≻ (begin-
        (define-syntax- x (make-variable-like-transformer #'x-/props))
        (ro:define x- e-))]]
  ;; function with no rest argument
  [(_ (f:id [x:id : τ_in] ... [kw:keyword y:id : τ_kw e_def:expr] ...)
      :-> τ_out
      body ...+) ≫
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (quasisyntax/loc this-syntax
                (λ ([x : τ_in] ... [kw y : τ_kw e_def] ...)
                  #,(syntax/loc (stx-car #'(body ...)) (ann body* : τ_out))))
   --------
   [≻ (define f : (C→ τ_in ... [kw τ_kw] ... τ_out)
        lam)]]
  ;; function with rest argument
  [(_ (f:id [x:id : τ_in] ... [kw:keyword y:id : τ_kw e_def:expr] ... . [rst:id : τ_rst])
      :-> τ_out
      body ...+) ≫
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (quasisyntax/loc this-syntax
                (λ ([x : τ_in] ... [kw y : τ_kw e_def] ... . [rst : τ_rst])
                  #,(syntax/loc (stx-car #'(body ...)) (ann body* : τ_out))))
   --------
   [≻ (define f : (C→* [τ_in ...] [[kw τ_kw] ...] #:rest τ_rst τ_out)
        lam)]]
  ;; function with type declaration beforehand
  [(_ (f:id/type-decl
       . (~and args (~or (:id ... (~seq :keyword [:id :expr]) ...)
                         (:id ... (~seq :keyword [:id :expr]) ... . :id))))
      body ...+) ≫
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (syntax/loc this-syntax (λ args body*))
   --------
   [≻ (define f lam)]])

(define-typed-syntax define/conc
  #:datum-literals [:]
  ;; function with no rest argument
  [(_ (f:id [x:id : τ_in] ... [kw:keyword y:id : τ_kw e_def:expr] ...)
      :-> τ_out
      body ...+) ≫
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (quasisyntax/loc this-syntax
                (λ/conc ([x : τ_in] ... [kw y : τ_kw e_def] ...)
                  #,(syntax/loc (stx-car #'(body ...)) (ann body* : τ_out))))
   --------
   [≻ (define f : (C→/conc τ_in ... [kw τ_kw] ... τ_out)
        lam)]]
  ;; function with rest argument
  [(_ (f:id [x:id : τ_in] ... [kw:keyword y:id : τ_kw e_def:expr] ... . [rst:id : τ_rst])
      :-> τ_out
      body ...+) ≫
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (quasisyntax/loc this-syntax
                (λ/conc ([x : τ_in] ... [kw y : τ_kw e_def] ... . [rst : τ_rst])
                  #,(syntax/loc (stx-car #'(body ...)) (ann body* : τ_out))))
   --------
   [≻ (define f : (C→** [τ_in ...] [[kw τ_kw] ...] #:rest τ_rst τ_out)
        lam)]]
  ;; function with type declaration beforehand
  [(_ (f:id/type-decl
       . (~and args (~or (:id ... (~seq :keyword [:id :expr]) ...)
                         (:id ... (~seq :keyword [:id :expr]) ... . :id))))
      body ...+) ≫
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (syntax/loc this-syntax (λ/conc args body*))
   --------
   [≻ (define f lam)]])

;; This new version of λ handles keyword arguments.
;; λ type checks its body twice, once each assuming conc and sym path,
;; and thus may be applied in any type of path
(define-typed-syntax λ
  #:datum-literals [:]
  ;; need expected type, no rest argument
  [(_ (x:id ... (~seq kw:keyword [y:id e_def:expr]) ...) body)
   ⇐ (~C→* [τ_in ...] [[kw* τ_kw] ...] τ_out) ≫
   #:fail-unless (equal? (syntax->datum #'[kw ...])
                         (syntax->datum #'[kw* ...]))
   (format "keywords don't match, expected ~a, given ~a"
           (syntax->datum #'[kw* ...])
           (syntax->datum #'[kw ...]))
   #:do[(save-sym-path-info)
        (mk-path-sym)]
   ;; assume types are same in both kinds of paths, TODO: is this true?
   [⊢ [e_def ≫ e_def- ⇐ τ_kw] ...] ; default arg must be double-checked too
   [[x ≫ x-- : τ_in] ... [y ≫ y-- : τ_kw] ... ⊢ body ≫ body- ⇐ τ_out]
   #:do[(mk-path-conc)]
   [⊢ [e_def ≫ _ ⇐ τ_kw] ...]
   [[x ≫ _ : τ_in] ... [y ≫ _ : τ_kw] ... ⊢ body ≫ _ ⇐ τ_out]
   #:do[(restore-sym-path-info)]
   #:with [[x- ...] [y- ...]] (split-at* (stx->list #'[x-- ... y-- ...])
                                         (list (length (stx->list #'[x ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   ---------
   [⊢ (ro:λ (x- ... kw-arg- ... ...) body-)]]
  ;; need expected type, no rest argument, concrete path only
  [(_ (arg ...) body)
   ⇐ (~C→** [τ_in ...] [[kw* τ_kw] ...] τ_out) ≫
   ---------
   [≻ (λ/conc (arg ...) body)]]
  ;; need expected type, with rest argument
  [(_ (x:id ... . rst:id) e)
   ⇐ (~C→* [τ_in ...] [] #:rest τ_rst τ_out) ≫
   #:do[(save-sym-path-info)
        (mk-path-sym)]
   ;; assume types are same in both kinds of paths, TODO: is this true?
   [[x ≫ x-- : τ_in] ... [rst ≫ rst-- : τ_rst] ⊢ e ≫ e- ⇐ τ_out]
   #:do[(mk-path-conc)]
   [[x ≫ _ : τ_in] ... [rst ≫ _ : τ_rst] ⊢ e ≫ _ ⇐ τ_out]
   #:do[(restore-sym-path-info)]
   #:with [[x- ...] [rst-]] (split-at* (stx->list #'[x-- ... rst--])
                                       (list (length (stx->list #'[x ...]))))
   ---------
   [⊢ (ro:λ (x- ... . rst-) e-)]]
  ;; use case-> expected type, no rest argument
  [(_ (~and args (~or (x:id ... (~seq kw:keyword [y:id e_def:expr]) ...)
                      (x:id ... (~seq kw:keyword [y:id e_def:expr]) ... . rst:id)))
     body)
   ⇐ (~Ccase-> τ_expected ...) ≫
   #:fail-unless (stx-andmap (C→-arity-is? (stx-length #'[x ...])
                                           (syntax->datum #'[kw ...])
                                           (not (false? (attribute rst))))
                             #'[τ_expected ...])
   "wrong number of arguments"
   #:with τ_unionized (C→-map-union #'[τ_expected ...])
   #:do[(save-sym-path-info)
        (mk-path-sym)]
   ;; assume types are same in both kinds of paths, TODO: is this true?
   [⊢ (λ args body) ≫ _ ⇐ τ_expected] ...
   [⊢ (λ args body) ≫ f- ⇐ τ_unionized]
   #:do[(mk-path-conc)]
   [⊢ (λ args body) ≫ _ ⇐ τ_expected] ...
   [⊢ (λ args body) ≫ _ ⇐ τ_unionized]
   #:do[(restore-sym-path-info)]
   ---------
   [⊢ f-]]
  ;; no expected type, keyword arguments
  [(_ ([x:id : τ_in:type] ... [kw:keyword y:id : τ_kw:type e_def:expr] ...)
      body) ≫
   #:do[(save-sym-path-info)
        (mk-path-sym)]
   ;; assume types are same in both kinds of paths, TODO: is this true?
   [⊢ [e_def ≫ e_def- ⇐ τ_kw.norm] ...]
   [[x ≫ x-- : τ_in.norm] ... [y ≫ y-- : τ_kw.norm] ... ⊢ body ≫ body- ⇒ τ_out]
   #:do[(mk-path-conc)]
   [⊢ [e_def ≫ _ ⇐ τ_kw.norm] ...]
   [[x ≫ _ : τ_in.norm] ... [y ≫ _ : τ_kw.norm] ... ⊢ body ≫ _ ⇐ τ_out]
   #:do[(restore-sym-path-info)]
   #:with [[x- ...] [y- ...]] (split-at* (stx->list #'[x-- ... y-- ...])
                                         (list (length (stx->list #'[x ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   -------
   [⊢ (ro:λ (x- ... kw-arg- ... ...) body-)
      ⇒ (C→ τ_in ... [kw τ_kw] ... τ_out)]]
  ;; no expected type, rest argument
  [(_ ([x:id : τ_in:type] ... [kw:keyword y:id : τ_kw:type e_def:expr] ... . [rst:id : τ_rst:type])
      body) ≫
   #:do[(save-sym-path-info)
        (mk-path-sym)]
   ;; assume types are same in both kinds of paths, TODO: is this true?
   [⊢ [e_def ≫ e_def- ⇐ τ_kw.norm] ...]
   [[x ≫ x-- : τ_in.norm] ... [y ≫ y-- : τ_kw.norm] ... [rst ≫ rst-- : τ_rst.norm]
    ⊢ body ≫ body- ⇒ τ_out]
   #:do[(mk-path-conc)]
   [⊢ [e_def ≫ _ ⇐ τ_kw.norm] ...]
   [[x ≫ _ : τ_in.norm] ... [y ≫ _ : τ_kw.norm] ... [rst ≫ _ : τ_rst.norm]
    ⊢ body ≫ _ ⇐ τ_out]
   #:do[(restore-sym-path-info)]
   #:with [[x- ...] [y- ...] [rst-]]
   (split-at* (stx->list #'[x-- ... y-- ... rst--])
              (list (length (stx->list #'[x ...]))
                    (length (stx->list #'[y ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   -------
   [⊢ (ro:λ (x- ... kw-arg- ... ... . rst-) body-)
      ⇒ (C→* [τ_in.norm ...] [[kw τ_kw.norm] ...] #:rest τ_rst.norm τ_out)]])

;; produces fns that may only be applied in concrete paths
(define-typed-syntax λ/conc
  #:datum-literals [:]
  ;; need expected type, no rest argument
  [(_ (x:id ... (~seq kw:keyword [y:id e_def:expr]) ...) body)
   ⇐ (~C→** [τ_in ...] [[kw* τ_kw] ...] τ_out) ≫
   #:fail-unless (equal? (syntax->datum #'[kw ...])
                         (syntax->datum #'[kw* ...]))
   (format "keywords don't match, expected ~a, given ~a"
           (syntax->datum #'[kw* ...])
           (syntax->datum #'[kw ...]))
   #:do[(save-sym-path-info)
        (mk-path-conc)]
   [⊢ [e_def ≫ e_def- ⇐ τ_kw] ...]
   [[x ≫ x-- : τ_in] ... [y ≫ y-- : τ_kw] ... ⊢ body ≫ body- ⇐ τ_out]
   #:do[(restore-sym-path-info)]
   #:with [[x- ...] [y- ...]] (split-at* (stx->list #'[x-- ... y-- ...])
                                         (list (length (stx->list #'[x ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   ---------
   [⊢ (ro:λ (x- ... kw-arg- ... ...) body-)]]
  ;; need expected type, with rest argument
  [(_ (x:id ... . rst:id) e)
   ⇐ (~C→** [τ_in ...] [] #:rest τ_rst τ_out) ≫
   #:do[(save-sym-path-info)
        (mk-path-conc)]
   [[x ≫ x-- : τ_in] ... [rst ≫ rst-- : τ_rst] ⊢ e ≫ e- ⇐ τ_out]
   #:do[(restore-sym-path-info)]
   #:with [[x- ...] [rst-]] (split-at* (stx->list #'[x-- ... rst--])
                                       (list (length (stx->list #'[x ...]))))
   ---------
   [⊢ (ro:λ (x- ... . rst-) e-)]]
  ;; use case-> expected type, no rest argument
  [(_ (~and args (~or (x:id ... (~seq kw:keyword [y:id e_def:expr]) ...)
                      (x:id ... (~seq kw:keyword [y:id e_def:expr]) ... . rst:id)))
     body)
   ⇐ (~Ccase-> τ_expected ...) ≫
   #:fail-unless (stx-andmap (C→-arity-is? (stx-length #'[x ...])
                                           (syntax->datum #'[kw ...])
                                           (not (false? (attribute rst))))
                             #'[τ_expected ...])
   "wrong number of arguments"
   #:with τ_unionized (C→-map-union #'[τ_expected ...])
   #:do[(save-sym-path-info)
        (mk-path-conc)]
   [⊢ (λ/conc args body) ≫ _ ⇐ τ_expected] ...
   [⊢ (λ/conc args body) ≫ f- ⇐ τ_unionized]
   #:do[(restore-sym-path-info)]
   ---------
   [⊢ f-]]
  ;; no expected type, keyword arguments
  [(_ ([x:id : τ_in:type] ... [kw:keyword y:id : τ_kw:type e_def:expr] ...)
      body) ≫
   #:do[(save-sym-path-info)
        (mk-path-conc)]
   [⊢ [e_def ≫ e_def- ⇐ τ_kw.norm] ...]
   [[x ≫ x-- : τ_in.norm] ... [y ≫ y-- : τ_kw.norm] ... ⊢ body ≫ body- ⇒ τ_out]
   #:do[(restore-sym-path-info)]
   #:with [[x- ...] [y- ...]] (split-at* (stx->list #'[x-- ... y-- ...])
                                         (list (length (stx->list #'[x ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   -------
   [⊢ (ro:λ (x- ... kw-arg- ... ...) body-)
      ⇒ (C→/conc τ_in ... [kw τ_kw] ... τ_out)]]
  ;; no expected type, rest argument
  [(_ ([x:id : τ_in:type] ... [kw:keyword y:id : τ_kw:type e_def:expr] ... . [rst:id : τ_rst:type])
      body) ≫
   #:do[(save-sym-path-info)
        (mk-path-conc)]
   [⊢ [e_def ≫ e_def- ⇐ τ_kw.norm] ...]
   [[x ≫ x-- : τ_in.norm] ... [y ≫ y-- : τ_kw.norm] ... [rst ≫ rst-- : τ_rst.norm]
    ⊢ body ≫ body- ⇒ τ_out]
   #:do[(restore-sym-path-info)]
   #:with [[x- ...] [y- ...] [rst-]]
   (split-at* (stx->list #'[x-- ... y-- ... rst--])
              (list (length (stx->list #'[x ...]))
                    (length (stx->list #'[y ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   -------
   [⊢ (ro:λ (x- ... kw-arg- ... ... . rst-) body-)
      ⇒ (C→** [τ_in.norm ...] [[kw τ_kw.norm] ...] #:rest τ_rst.norm τ_out)]])

;; ----------------------------------------------------------------------------

;; Begin

(define-typed-syntax begin
  [(_ e_unit ... e) ⇐ τ_expected ≫
   [⊢ e_unit ≫ e_unit- ⇒ _] ...
   [⊢ e ≫ e- ⇐ τ_expected]
   #:with stx- (transfer-props #'e- #'(begin- e_unit- ... e-))
   --------
   [⊢ stx-]]
  [(_ e_unit ... e) ≫
   [⊢ e_unit ≫ e_unit- ⇒ _] ...
   [⊢ e ≫ e- ⇒ τ_e]
   #:with stx- (transfer-props #'e- #'(begin- e_unit- ... e-))
   --------
   [⊢ stx- ⇒ τ_e]])

;; ----------------------------------------------------------------------------

;; Lists

(define-typed-syntax list
  [(_ e ...) ≫
   [⊢ [e ≫ e- ⇒ : τ] ...]
   --------
   [⊢ [_ ≫ (ro:#%app ro:list e- ...) ⇒ : (CList τ ...)]]])

;; ----------------------------------------------------------------------------

;; Function Application

(begin-for-syntax
  (define (expected-arguments-string τ_f)
    (syntax-parse τ_f
      [(~C→* [τ_a ...] [] _) 
       (string-join (stx-map type->str #'[τ_a ...]) ", ")]
      [(~C→** [τ_a ...] [] _) 
       (string-join (stx-map type->str #'[τ_a ...]) ", ")]
      [(~C→* [τ_a ...] [] #:rest τ_rst _) 
       (format
        "~a, @ ~a"
        (string-join (stx-map type->str #'[τ_a ...]) ", ")
        (type->str #'τ_rst))]
      [(~C→** [τ_a ...] [] #:rest τ_rst _) 
       (format
        "~a, @ ~a"
        (string-join (stx-map type->str #'[τ_a ...]) ", ")
        (type->str #'τ_rst))]
      [(~C→* [τ_a ...] [[kw τ_b] ...] _)
       (format
        "~a [, ~a ]"
        (string-join (stx-map type->str #'[τ_a ...]) ", ")
        (string-join
         (stx-map
          (λ (kw τ_b)
            (format "~s ~a" (syntax->datum kw) (type->str τ_b)))
          #'[kw ...]
          #'[τ_b ...])
         ", "))]
      [(~C→** [τ_a ...] [[kw τ_b] ...] _)
       (format
        "~a [, ~a ]"
        (string-join (stx-map type->str #'[τ_a ...]) ", ")
        (string-join
         (stx-map
          (λ (kw τ_b)
            (format "~s ~a" (syntax->datum kw) (type->str τ_b)))
          #'[kw ...]
          #'[τ_b ...])
         ", "))]
      [(~C→* [τ_a ...] [[kw τ_b] ...] #:rest τ_rst _)
       (format
        "~a [, ~a ], @ ~a"
        (string-join (stx-map type->str #'[τ_a ...]) ", ")
        (string-join
         (stx-map
          (λ (kw τ_b)
            (format "~s ~a" (syntax->datum kw) (type->str τ_b)))
          #'[kw ...]
          #'[τ_b ...])
         ", ")
        (type->str #'τ_rst))]
      [(~C→** [τ_a ...] [[kw τ_b] ...] #:rest τ_rst _)
       (format
        "~a [, ~a ], @ ~a"
        (string-join (stx-map type->str #'[τ_a ...]) ", ")
        (string-join
         (stx-map
          (λ (kw τ_b)
            (format "~s ~a" (syntax->datum kw) (type->str τ_b)))
          #'[kw ...]
          #'[τ_b ...])
         ", ")
        (type->str #'τ_rst))])))

(define-typed-syntax app
  ;; concrete function, any path, no rest arg
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   ;[⊢ f ≫ f-- ⇒ (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...] τ_out) ~!)]
;   #:do[(displayln (stx->datum #'f))]
   #:with f-- (expand/ro #'f)
   #:with (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...]
                      τ_out
                      : #:+ posprop #:- negprop)
                ~!)
   (typeof #'f--)
   #:with f- (replace-stx-loc #'f-- #'f)
   #:fail-unless (stx-length=? #'[a ...] #'[τ_a ...])
   (num-args-fail-msg #'f #'[τ_a ...] #'[a ...])
   #:do [(define kws/τs*
           (for/list ([kw* (in-list (syntax->datum #'[kw* ...]))]
                      [τ* (in-list (syntax->list #'[τ_kw* ...]))])
             (list kw* τ*)))]
   #:with [τ_b ...]
   (for/list ([kw (in-list (syntax->list #'[kw ...]))])
     (define p (assoc (syntax-e kw) kws/τs*))
     (unless p (raise-syntax-error #f "keyword not in domain of function" kw))
     (second p))
   ;[⊢ [a ≫ a- ⇐ τ_a] ...]
   ;[⊢ [b ≫ b- ⇐ τ_b] ...]
   #:with [a- ...] (stx-map expand/ro #'[a ...])
   #:with [b- ...] (stx-map expand/ro #'[b ...])
   #:with [τ_a* ...] (stx-map typeof #'(a- ...))
   #:with [τ_b* ...] (stx-map typeof #'(b- ...))
   #:fail-unless (typechecks? #'[τ_a* ... τ_b* ...] #'[τ_a ... τ_b ...])
   (typecheck-fail-msg/multi #'[τ_a ... τ_b ...] #'[τ_a* ... τ_b* ...]
                             #'[a ... b ...])
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   #:do [(define prop-inst (prop-instantiate (stx-map get-arg-obj #'[a- ...])))]
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...)
      (⇒ : τ_out)
      (⇒ prop+ #,(syntax-local-introduce (prop-inst #'posprop)))
      (⇒ prop- #,(syntax-local-introduce (prop-inst #'negprop)))]]
  ;; concrete function, any path, with rest arg
  [(_ f:expr ab:expr ... (~seq kw:keyword c:expr) ...) ≫
   ;[⊢ f ≫ f-- ⇒ (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...] #:rest τ_rst τ_out) ~!)]
   #:with f-- (expand/ro #'f)
   #:with (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...] #:rest τ_rst τ_out
                      : #:+ posprop #:- negprop) ~!)
   (typeof #'f--)
   #:with f- (replace-stx-loc #'f-- #'f)
   #:fail-unless (stx-length>=? #'[ab ...] #'[τ_a ...])
   (num-args-fail-msg #'f #'[τ_a ...] #'[ab ...])
   #:with [[a ...] [b ...]]
   (split-at* (stx->list #'[ab ...])
              (list (stx-length #'[τ_a ...])))
   #:do [(define kws/τs*
           (for/list ([kw* (in-list (syntax->datum #'[kw* ...]))]
                      [τ* (in-list (syntax->list #'[τ_kw* ...]))])
             (list kw* τ*)))]
   #:with [τ_c ...]
   (for/list ([kw (in-list (syntax->list #'[kw ...]))])
     (define p (assoc (syntax-e kw) kws/τs*))
     (unless p (raise-syntax-error #f "keyword not in domain of function" kw))
     (second p))
   ;[⊢ [a ≫ a- ⇐ τ_a] ...]
   ;[⊢ (list b ...) ≫ rst- ⇐ τ_rst]
   ;[⊢ [c ≫ c- ⇐ τ_c] ...]
   #:with [a- ...] (stx-map expand/ro #'[a ...])
   #:with rst- (expand/ro #'(list b ...))
   #:with [c- ...] (stx-map expand/ro #'[c ...])
   #:with [τ_a* ...] (stx-map typeof #'(a- ...))
   #:with τ_rst* (typeof #'rst-)
   #:with [τ_c* ...] (stx-map typeof #'(c- ...))
   #:fail-unless (typechecks? #'[τ_a* ... τ_c* ... τ_rst*]
                              #'[τ_a ... τ_c ... τ_rst])
   (typecheck-fail-msg/multi #'[τ_a ... τ_c ... τ_rst]
                             #'[τ_a* ... τ_c* ... τ_rst*]
                             #'[a ... c ... (list b ...)])
   #:with [[kw/c- ...] ...] #'[[kw c-] ...]
   #:do [(define prop-inst (prop-instantiate (stx-map get-arg-obj #'[a- ...])))]
   --------
   [⊢ (ro:#%app ro:apply f- a- ... rst- kw/c- ... ...)
      (⇒ : τ_out)
      (⇒ prop+ #,(syntax-local-introduce (prop-inst #'posprop)))
      (⇒ prop- #,(syntax-local-introduce (prop-inst #'negprop)))]]
  ;; concrete function, conc path, no rest arg
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   ;[⊢ f ≫ f-- ⇒ (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...] τ_out) ~!)]
;   #:do[(displayln (stx->datum #'f))]
   #:with f-- (expand/ro #'f)
   #:with (~and (~C→** [τ_a ...] [[kw* τ_kw*] ...]
                      τ_out
                      : #:+ posprop #:- negprop)
                ~!)
   (typeof #'f--)
   #:fail-when (current-sym-path?) (conc-fn-msg)
   #:with f- (replace-stx-loc #'f-- #'f)
   #:fail-unless (stx-length=? #'[a ...] #'[τ_a ...])
   (num-args-fail-msg #'f #'[τ_a ...] #'[a ...])
   #:do [(define kws/τs*
           (for/list ([kw* (in-list (syntax->datum #'[kw* ...]))]
                      [τ* (in-list (syntax->list #'[τ_kw* ...]))])
             (list kw* τ*)))]
   #:with [τ_b ...]
   (for/list ([kw (in-list (syntax->list #'[kw ...]))])
     (define p (assoc (syntax-e kw) kws/τs*))
     (unless p (raise-syntax-error #f "keyword not in domain of function" kw))
     (second p))
   ;[⊢ [a ≫ a- ⇐ τ_a] ...]
   ;[⊢ [b ≫ b- ⇐ τ_b] ...]
   #:with [a- ...] (stx-map expand/ro #'[a ...])
   #:with [b- ...] (stx-map expand/ro #'[b ...])
   #:with [τ_a* ...] (stx-map typeof #'(a- ...))
   #:with [τ_b* ...] (stx-map typeof #'(b- ...))
   #:fail-unless (typechecks? #'[τ_a* ... τ_b* ...] #'[τ_a ... τ_b ...])
   (typecheck-fail-msg/multi #'[τ_a ... τ_b ...] #'[τ_a* ... τ_b* ...]
                             #'[a ... b ...])
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   #:do [(define prop-inst (prop-instantiate (stx-map get-arg-obj #'[a- ...])))]
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...)
      (⇒ : τ_out)
      (⇒ prop+ #,(syntax-local-introduce (prop-inst #'posprop)))
      (⇒ prop- #,(syntax-local-introduce (prop-inst #'negprop)))]]
  ;; concrete function, conc path, with rest arg
  [(_ f:expr ab:expr ... (~seq kw:keyword c:expr) ...) ≫
   ;[⊢ f ≫ f-- ⇒ (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...] #:rest τ_rst τ_out) ~!)]
   #:with f-- (expand/ro #'f)
   #:with (~and (~C→** [τ_a ...] [[kw* τ_kw*] ...] #:rest τ_rst τ_out
                      : #:+ posprop #:- negprop) ~!)
   (typeof #'f--)
   #:fail-when (current-sym-path?) (conc-fn-msg)
   #:with f- (replace-stx-loc #'f-- #'f)
   #:fail-unless (stx-length>=? #'[ab ...] #'[τ_a ...])
   (num-args-fail-msg #'f #'[τ_a ...] #'[ab ...])
   #:with [[a ...] [b ...]]
   (split-at* (stx->list #'[ab ...])
              (list (stx-length #'[τ_a ...])))
   #:do [(define kws/τs*
           (for/list ([kw* (in-list (syntax->datum #'[kw* ...]))]
                      [τ* (in-list (syntax->list #'[τ_kw* ...]))])
             (list kw* τ*)))]
   #:with [τ_c ...]
   (for/list ([kw (in-list (syntax->list #'[kw ...]))])
     (define p (assoc (syntax-e kw) kws/τs*))
     (unless p (raise-syntax-error #f "keyword not in domain of function" kw))
     (second p))
   ;[⊢ [a ≫ a- ⇐ τ_a] ...]
   ;[⊢ (list b ...) ≫ rst- ⇐ τ_rst]
   ;[⊢ [c ≫ c- ⇐ τ_c] ...]
   #:with [a- ...] (stx-map expand/ro #'[a ...])
   #:with rst- (expand/ro #'(list b ...))
   #:with [c- ...] (stx-map expand/ro #'[c ...])
   #:with [τ_a* ...] (stx-map typeof #'(a- ...))
   #:with τ_rst* (typeof #'rst-)
   #:with [τ_c* ...] (stx-map typeof #'(c- ...))
   #:fail-unless (typechecks? #'[τ_a* ... τ_c* ... τ_rst*]
                              #'[τ_a ... τ_c ... τ_rst])
   (typecheck-fail-msg/multi #'[τ_a ... τ_c ... τ_rst]
                             #'[τ_a* ... τ_c* ... τ_rst*]
                             #'[a ... c ... (list b ...)])
   #:with [[kw/c- ...] ...] #'[[kw c-] ...]
   #:do [(define prop-inst (prop-instantiate (stx-map get-arg-obj #'[a- ...])))]
   --------
   [⊢ (ro:#%app ro:apply f- a- ... rst- kw/c- ... ...)
      (⇒ : τ_out)
      (⇒ prop+ #,(syntax-local-introduce (prop-inst #'posprop)))
      (⇒ prop- #,(syntax-local-introduce (prop-inst #'negprop)))]]
  ;; concrete case->
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   ;[⊢ f ≫ f- ⇒ (~and (~Ccase-> ~! τ_f ...) ~!)]
   #:with f-- (expand/ro #'f)
   #:with (~Ccase-> ~! τ_f ...) (typeof #'f--)
   #:with f- (replace-stx-loc #'f-- #'f)
   ;[⊢ [a ≫ a- ⇒ τ_a] ...]
   ;[⊢ [b ≫ b- ⇒ τ_b] ...]
   #:with [a- ...] (stx-map expand/ro #'[a ...])
   #:with [b- ...] (stx-map expand/ro #'[b ...])
   #:with [τ_a ...] (stx-map typeof #'(a- ...))
   #:with [τ_b ...] (stx-map typeof #'(b- ...))
   #:with result-info
   (for/or ([τ_f (in-list (stx->list #'[τ_f ...]))])
     (syntax-parse τ_f
       [(~C→* [τ_a* ...] [[kw* τ_kw*] ...] τ_out
              : #:+ posprop #:- negprop)
        (define kws/τs*
          (for/list ([kw (in-list (syntax->datum #'[kw* ...]))]
                     [τ (in-list (syntax->list #'[τ_kw* ...]))])
            (list kw τ)))
        (and (typechecks? #'[τ_a ...] #'[τ_a* ...])
             (for/and ([kw (in-list (syntax->datum #'[kw ...]))]
                       [τ_b (in-list (syntax->list #'[τ_b ...]))])
               (define p (assoc kw kws/τs*))
               (and p
                    (typecheck? τ_b (second p))))
             (list #'τ_out #'posprop #'negprop))]
       [(~C→** [τ_a* ...] [[kw* τ_kw*] ...] τ_out
               : #:+ posprop #:- negprop)
        #:when (not (current-sym-path?))
        (define kws/τs*
          (for/list ([kw (in-list (syntax->datum #'[kw* ...]))]
                     [τ (in-list (syntax->list #'[τ_kw* ...]))])
            (list kw τ)))
        (and (typechecks? #'[τ_a ...] #'[τ_a* ...])
             (for/and ([kw (in-list (syntax->datum #'[kw ...]))]
                       [τ_b (in-list (syntax->list #'[τ_b ...]))])
               (define p (assoc kw kws/τs*))
               (and p
                    (typecheck? τ_b (second p))))
             (list #'τ_out #'posprop #'negprop))]
       [(~C→* [τ_a* ...] [[kw* τ_kw*] ...] #:rest τ_rst* τ_out
              : #:+ posprop #:- negprop)
        #:when (stx-length>=? #'[τ_a ...] #'[τ_a* ...])
        #:with [[τ_fst ...] [τ_rst ...]]
        (split-at* (stx->list #'[τ_a ...]) (list (stx-length #'[τ_a* ...])))
        (define kws/τs*
          (for/list ([kw (in-list (syntax->datum #'[kw* ...]))]
                     [τ (in-list (syntax->list #'[τ_kw* ...]))])
            (list kw τ)))
        (and (typechecks? #'[τ_fst ...] #'[τ_a* ...])
             (typecheck? ((current-type-eval) #'(CList τ_rst ...)) #'τ_rst*)
             (for/and ([kw (in-list (syntax->datum #'[kw ...]))]
                       [τ_b (in-list (syntax->list #'[τ_b ...]))])
               (define p (assoc kw kws/τs*))
               (and p
                    (typecheck? τ_b (second p))))
             (list #'τ_out #'posprop #'negprop))]
       [_ #false]))
   #:fail-unless (syntax-e #'result-info)
   ; use (failing) typechecks? to get err msg
   (let* ([τs_given #'(τ_a ...)]
          [expressions #'(a ...)])
     (format (string-append "type mismatch\n"
                            "  expected one of:\n"
                            "    ~a\n"
                            "  given: ~a\n"
                            "  expressions: ~a")
       (string-join
        (stx-map expected-arguments-string #'[τ_f ...])
        "\n    ")
       (string-join (stx-map type->str τs_given) ", ")
       (string-join (map ~s (stx-map syntax->datum expressions)) ", ")))
   #:with [τ_out posprop negprop] #'result-info
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   #:do [(define prop-inst (prop-instantiate (stx-map get-arg-obj #'[a- ...])))]
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...)
      (⇒ : τ_out)
      (⇒ prop+ #,(syntax-local-introduce (prop-inst #'posprop)))
      (⇒ prop- #,(syntax-local-introduce (prop-inst #'negprop)))]]
  ;; concrete union functions
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   ;[⊢ [f ≫ f-- ⇒ : (~and (~CU* τ_f ...) ~!)]]
   #:with f-- (expand/ro #'f)
   #:with (~CU* ~! τ_f ...) (typeof #'f--)
   #:with f- (replace-stx-loc #'f-- #'f)
   ;[⊢ [a ≫ a- ⇒ : τ_a] ...]
   ;[⊢ [b ≫ b- ⇒ : τ_b] ...]
   #:with (a- ...) (stx-map expand/ro #'(a ...))
   #:with (b- ...) (stx-map expand/ro #'(b ...))
   #:with (τ_a ...) (stx-map typeof #'(a- ...))
   #:with (τ_b ...) (stx-map typeof #'(b- ...))
   #:with f* (generate-temporary #'f)
   #:with (a* ...) (generate-temporaries #'(a ...))
   #:with (b* ...) (generate-temporaries #'(b ...))
   #:with [[kw/b* ...] ...] #'[[kw b*] ...]
   [([f* ≫ _ : τ_f] [a* ≫ _ : τ_a] ... [b* ≫ _ : τ_b] ...)
    ⊢ [(app f* a* ... kw/b* ... ...) ≫ _ ⇒ : τ_out]]
   ...
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...) ⇒ (CU τ_out ...)]]
  ;; symbolic functions
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   ;[⊢ [f ≫ f-- ⇒ : (~and (~U* τ_f ...) ~!)]]
   #:with f-- (expand/ro #'f)
   #:with (~U* ~! τ_f ...) (typeof #'f--)
   #:with f- (replace-stx-loc #'f-- #'f)
   ;[⊢ [a ≫ a- ⇒ : τ_a] ...]
   ;[⊢ [b ≫ b- ⇒ : τ_b] ...]
   #:with (a- ...) (stx-map expand/ro #'(a ...))
   #:with (b- ...) (stx-map expand/ro #'(b ...))
   #:with (τ_a ...) (stx-map typeof #'(a- ...))
   #:with (τ_b ...) (stx-map typeof #'(b- ...))
   #:with f* (generate-temporary #'f)
   #:with (a* ...) (generate-temporaries #'(a ...))
   #:with (b* ...) (generate-temporaries #'(b ...))
   #:with [[kw/b* ...] ...] #'[[kw b*] ...]
   [([f* ≫ _ : τ_f] [a* ≫ _ : τ_a] ... [b* ≫ _ : τ_b] ...)
    ⊢ [#,(syntax/loc this-syntax (app f* a* ... kw/b* ... ...)) ≫ _ ⇒ : τ_out]]
   ...
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...) ⇒ (U τ_out ...)]]
  ;; symbolic constant and functions
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   ;[⊢ [f ≫ f-- ⇒ : (~and (~Constant* (~U* τ_f ...)) ~!)]]
   #:with f-- (expand/ro #'f)
   #:with (~or (~Term* τ_f)
               (~Constant* (~Term* τ_f)))
   (typeof #'f--)
   #:with f- (replace-stx-loc #'f-- #'f)
   ;[⊢ [a ≫ a- ⇒ : τ_a] ...]
   ;[⊢ [b ≫ b- ⇒ : τ_b] ...]
   #:with (a- ...) (stx-map expand/ro #'(a ...))
   #:with (b- ...) (stx-map expand/ro #'(b ...))
   #:with (τ_a ...) (stx-map typeof #'(a- ...))
   #:with (τ_b ...) (stx-map typeof #'(b- ...))
   #:with f* (generate-temporary #'f)
   #:with (a* ...) (generate-temporaries #'(a ...))
   #:with (b* ...) (generate-temporaries #'(b ...))
   #:with [[kw/b* ...] ...] #'[[kw b*] ...]
   [([f* ≫ _ : τ_f] [a* ≫ _ : τ_a] ... [b* ≫ _ : τ_b] ...)
    ⊢ [(app f* a* ... kw/b* ... ...) ≫ _ ⇒ : τ_out]]
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   --------
   [⊢ [_ ≫ (ro:#%app f- a- ... kw/b- ... ...) ⇒ : τ_out]]])

;; ----------------------------------------------------------------------------

;; Apply

;; This version of apply is very limited: it only works with
;; functions that declare a rest argument.

(define-typed-syntax apply
  [(_ f:expr lst:expr) ≫
   [⊢ f ≫ f- ⇒ (~C→* [] [] #:rest τ_rst τ_out)]
   [⊢ lst ≫ lst- ⇐ τ_rst]
   --------
   [⊢ (ro:apply f- lst-) ⇒ τ_out]]
  [(_ f:expr lst:expr) ≫
   [⊢ f ≫ f- ⇒ (~Ccase-> ~! τ_f ...)]
   [⊢ lst ≫ lst- ⇒ τ_lst]
   #:with τ_out
   (for/or ([τ_f (in-list (stx->list #'[τ_f ...]))])
     (syntax-parse τ_f
       [(~C→* [] [] #:rest τ_rst* τ_out)
        (and (typecheck? #'τ_lst #'τ_rst*)
             #'τ_out)]
       [(~C→** [] [] #:rest τ_rst* τ_out)
        #:when (not (current-sym-path?))
        (and (typecheck? #'τ_lst #'τ_rst*)
             #'τ_out)]
       [_ #false]))
   #:fail-unless (syntax-e #'τ_out) "none of the cases matched"
   --------
   [⊢ (ro:apply f- lst-) ⇒ τ_out]])

;; ----------------------------------------------------------------------------

;; Variable Assignment

;; disallow mutation of concrete-typed variables when under symbolic path
(define-typed-syntax set!
  [(set! x:id e:expr) ≫
   [⊢ x ≫ x- ⇒ τ_x]
   #:fail-when (no-mutate? #'x-)  (no-mut-msg "variable ~a" (stx->datum #'x))
   [⊢ e ≫ e- ⇐ τ_x]
   --------
   [⊢ (ro:set! x- e-) ⇒ CUnit]])

;; ----------------------------------------------------------------------------

;; This version of let allows declaring variables as mutable

(define-typed-syntax let
  #:datum-literals [:]
  [(_ name:id ([x:id : τ_x:type e:expr] ...) :-> ~! τ_out:type b ...+) ≫
   [⊢ [e ≫ e- ⇐ τ_x] ...]
   #:with body (syntax/loc this-syntax (begin b ...))
   [[name ≫ name- : (C→ τ_x ... τ_out)]
    [x ≫ x- : τ_x] ...
    ⊢ body ≫ body- ⇐ τ_out]
   --------
   [⊢ (let- name- ([x- e-] ...) body-) ⇒ τ_out]]
  [(_ name:id ([x:id : τ_x:type e:expr] ...) b ...+) ⇐ τ_out ≫
   [⊢ [e ≫ e- ⇐ τ_x] ...]
   #:with body (syntax/loc this-syntax (begin b ...))
   [[name ≫ name- : (C→ τ_x ... τ_out)]
    [x ≫ x- : τ_x] ...
    ⊢ body ≫ body- ⇐ τ_out]
   --------
   [⊢ (let- name- ([x- e-] ...) body-)]]
  [(_ ([x m:mut-kw e] ...) e_body ...) ⇐ τ_expected ≫
   [⊢ [e ≫ e- ⇒ : τ_x] ...]
   #:with [τ_x* ...]
   (stx-map (λ (τ mut?) (if mut? (type-merge τ τ) τ))
            #'[τ_x ...]
            (attribute m.mutable?))
   [[x ≫ x- : τ_x* type-decl-mutable m.mutable?/tb] ...
    ⊢ (begin e_body ...) ≫ e_body- ⇐ τ_expected]
   --------
   [⊢ (ro:let ([x- e-] ...) e_body-)]]
  [(_ ([x m:mut-kw e] ...) e_body ...) ≫
   [⊢ [e ≫ e- ⇒ : τ_x] ...]
   #:with [τ_x* ...]
   (stx-map (λ (τ mut?) (if mut? (type-merge τ τ) τ))
            #'[τ_x ...]
            (attribute m.mutable?))
   [[x ≫ x- : τ_x* type-decl-mutable m.mutable?/tb] ...
    ⊢ (begin e_body ...) ≫ e_body- ⇒ τ_body]
   --------
   [⊢ (ro:let ([x- e-] ...) e_body-) ⇒ τ_body]])

;; ----------------------------------------------------------------------------
