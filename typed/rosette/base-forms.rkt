#lang turnstile

(provide : define λ apply ann begin list
         (rename-out [app #%app])
         unsafe-assign-type unsafe-define/assign-type
         (for-syntax expand/ro))

(require (only-in turnstile/examples/stlc+union ann begin)
         (prefix-in ro: rosette/safe)
         "types.rkt")

(begin-for-syntax
  ;; split-at* : [Listof A] [Listof Natural] -> [Listof [Listof A]]
  (define (split-at* lst lengths)
    (cond [(empty? lengths) (list lst)]
          [else
           (define-values [fst rst]
             (split-at lst (first lengths)))
           (cons fst (split-at* rst (rest lengths)))]))
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

;; Declaring Types before Definitions

(begin-for-syntax
  (define type-decl-internal-id 'type-decl-internal-id)
  (define type-decl-internal-id-for 'type-decl-internal-id-for)
  (define-syntax-class id/type-decl
    #:attributes [internal-id type]
    [pattern x:id
      ;; expand x in such a way that an unbound identifier
      ;; won't be an error
      #:with x* (local-expand #'x 'expression #false)
      #:attr internal-id (syntax-property #'x* type-decl-internal-id)
      #:when (attribute internal-id)
      #:with type (typeof #'x*)]))

(define-typed-syntax :
  #:datum-literals [:]
  [(_ x:id : τ) ≫
   #:with x- (generate-temporary #'x)
   --------
   [≻ (define-syntax- x
        (make-variable-like-transformer
         (set-stx-prop/preserved
          (set-stx-prop/preserved
           (⊢ x- : τ)
           type-decl-internal-id
           (syntax-local-introduce #'x-))
          type-decl-internal-id-for
          (syntax-local-introduce #'x))))]])

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
   #:with lam (syntax/loc this-syntax
                (λ ([x : τ_in] ... [kw y : τ_kw e_def] ...)
                  (ann body* : τ_out)))
   --------
   [≻ (define f : (C→ τ_in ... [kw τ_kw] ... τ_out)
        lam)]]
  ;; function with rest argument
  [(_ (f:id [x:id : τ_in] ... [kw:keyword y:id : τ_kw e_def:expr] ... . [rst:id : τ_rst])
      :-> τ_out
      body ...+) ≫
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (syntax/loc this-syntax
                (λ ([x : τ_in] ... [kw y : τ_kw e_def] ... . [rst : τ_rst])
                  (ann body* : τ_out)))
   --------
   [≻ (define f : (C→* [τ_in ...] [[kw τ_kw] ...] #:rest τ_rst τ_out)
        lam)]]
  ;; function with type declaration beforehand
  [(_ (f:id/type-decl . (~and args (:id ... (~seq :keyword [:id :expr]) ...))) body ...+) ≫
   #:with body* (syntax/loc this-syntax (begin body ...))
   #:with lam (syntax/loc this-syntax (λ args body*))
   --------
   [≻ (define f lam)]])

;; This new version of λ handles keyword arguments.

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
   [⊢ [e_def ≫ e_def- ⇐ τ_kw] ...]
   [[x ≫ x-- : τ_in] ... [y ≫ y-- : τ_kw] ... ⊢ body ≫ body- ⇐ τ_out]
   #:with [[x- ...] [y- ...]] (split-at* (stx->list #'[x-- ... y-- ...])
                                         (list (length (stx->list #'[x ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   ---------
   [⊢ (ro:λ (x- ... kw-arg- ... ...) body-)]]
  ;; need expected type, with rest argument
  [(_ (x:id ... . rst:id) e)
   ⇐ (~C→* [τ_in ...] [] #:rest τ_rst τ_out) ≫
   [[x ≫ x-- : τ_in] ... [rst ≫ rst-- : τ_rst]
    ⊢ e ≫ e- ⇐ τ_out]
   #:with [[x- ...] [rst-]] (split-at* (stx->list #'[x-- ... rst--])
                                       (list (length (stx->list #'[x ...]))))
   ---------
   [⊢ (ro:λ (x- ... . rst-) e-)]]
  ;; no expected type, keyword arguments
  [(_ ([x:id : τ_in:type] ... [kw:keyword y:id : τ_kw:type e_def:expr] ...)
      body) ≫
   [⊢ [e_def ≫ e_def- ⇐ τ_kw.norm] ...]
   [[x ≫ x-- : τ_in.norm] ... [y ≫ y-- : τ_kw.norm] ... ⊢ body ≫ body- ⇒ τ_out]
   #:with [[x- ...] [y- ...]] (split-at* (stx->list #'[x-- ... y-- ...])
                                         (list (length (stx->list #'[x ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   -------
   [⊢ (ro:λ (x- ... kw-arg- ... ...) body-)
      ⇒ (C→ τ_in ... [kw τ_kw] ... τ_out)]]
  ;; no expected type, rest argument
  [(_ ([x:id : τ_in:type] ... [kw:keyword y:id : τ_kw:type e_def:expr] ... . [rst:id : τ_rst:type])
      body) ≫
   [⊢ [e_def ≫ e_def- ⇐ τ_kw.norm] ...]
   [[x ≫ x-- : τ_in.norm] ... [y ≫ y-- : τ_kw.norm] ... [rst ≫ rst-- : τ_rst.norm]
    ⊢ body ≫ body- ⇒ τ_out]
   #:with [[x- ...] [y- ...] [rst-]]
   (split-at* (stx->list #'[x-- ... y-- ... rst--])
              (list (length (stx->list #'[x ...]))
                    (length (stx->list #'[y ...]))))
   #:with [[kw-arg- ...] ...] #'[[kw [y- e_def-]] ...]
   -------
   [⊢ (ro:λ (x- ... kw-arg- ... ... . rst-) body-)
      ⇒ (C→* [τ_in.norm ...] [[kw τ_kw.norm] ...] #:rest τ_rst.norm τ_out)]])

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
         ", "))])))

(define-typed-syntax app
  ;; concrete functions
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   ;[⊢ f ≫ f-- ⇒ (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...] τ_out) ~!)]
   #:with f-- (expand/ro #'f)
   #:with (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...] τ_out) ~!)
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
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...) ⇒ τ_out]]
  [(_ f:expr ab:expr ... (~seq kw:keyword c:expr) ...) ≫
   ;[⊢ f ≫ f-- ⇒ (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...] #:rest τ_rst τ_out) ~!)]
   #:with f-- (expand/ro #'f)
   #:with (~and (~C→* [τ_a ...] [[kw* τ_kw*] ...] #:rest τ_rst τ_out) ~!)
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
   --------
   [⊢ (ro:#%app ro:apply f- a- ... rst- kw/c- ... ...) ⇒ τ_out]]
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
   #:with τ_out
   (for/or ([τ_f (in-list (stx->list #'[τ_f ...]))])
     (syntax-parse τ_f
       [(~C→* [τ_a* ...] [[kw* τ_kw*] ...] τ_out)
        (define kws/τs*
          (for/list ([kw (in-list (syntax->datum #'[kw* ...]))]
                     [τ (in-list (syntax->list #'[τ_kw* ...]))])
            (list kw τ)))
        (and (typechecks? #'[τ_a ...] #'[τ_a* ...])
             (for/and ([kw (in-list (syntax->datum #'[kw ...]))]
                       [b (in-list (syntax->list #'[b ...]))])
               (define p (assoc kw kws/τs*))
               (and p
                    (typecheck? b (second p))))
             #'τ_out)]
       [_ #false]))
   #:fail-unless (syntax-e #'τ_out)
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
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...) ⇒ τ_out]]
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
    ⊢ [(app f* a* ... kw/b* ... ...) ≫ _ ⇒ : τ_out]]
   ...
   #:with [[kw/b- ...] ...] #'[[kw b-] ...]
   --------
   [⊢ (ro:#%app f- a- ... kw/b- ... ...) ⇒ (U τ_out ...)]]
  ;; symbolic constant functions
  [(_ f:expr a:expr ... (~seq kw:keyword b:expr) ...) ≫
   ;[⊢ [f ≫ f-- ⇒ : (~and (~Constant* (~U* τ_f ...)) ~!)]]
   #:with f-- (expand/ro #'f)
   #:with (~Constant* (~U* τ_f ...)) (typeof #'f--)
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
   [⊢ [_ ≫ (ro:#%app f- a- ... kw/b- ... ...) ⇒ : (U τ_out ...)]]])

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
   [⊢ f ≫ f- ⇒ (~Ccase-> τ_f ...)]
   [⊢ lst ≫ lst- ⇒ τ_lst]
   #:with τ_out
   (for/or ([τ_f (in-list (stx->list #'[τ_f ...]))])
     (syntax-parse τ_f
       [(~C→* [] [] #:rest τ_rst* τ_out)
        (and (typecheck? #'τ_lst #'τ_rst*)
             #'τ_out)]
       [_ #false]))
   #:fail-unless (syntax-e #'τ_out) "none of the cases matched"
   --------
   [⊢ (ro:apply f- lst-) ⇒ τ_out]])

;; ----------------------------------------------------------------------------

;; Unsafely assigning types to values

;; unsafe-assign-type doesn't typecheck anything within the expression
(define-typed-syntax unsafe-assign-type
  #:datum-literals [:]
  [(_ e:expr : τ:expr) ≫
   --------
   [⊢ e ⇒ : τ]])

(define-syntax-parser unsafe-define/assign-type
  #:datum-literals [:]
  [(_ x:id : τ:expr e:expr)
   #'(define x (unsafe-assign-type e : τ))])

