#lang turnstile

(provide match match-let
         _ var ?
         (for-syntax prop:match-pattern-id
                     match-pattern-id
                     macro/match-pattern-id
                     struct-predicate-accessor-pattern-id
                     ;; syntax classes
                     pat
                     pat-info
                     ;; other helpers
                     λ/pat-info
                     map-app3))

(require (postfix-in - rosette)
         "types.rkt"
         (only-in "base-forms.rkt" [#%app app*])
         (for-syntax lens/common
                     unstable/lens/syntax/stx
                     syntax/parse/class/local-value))

;; ------------------------------------------------------------------------

;; Match Patterns

;;  pat        ::= derived-pat
;;               | literal-pat
;;               | id-pat

;; derived-pat ::= match-pattern-id
;;               | (match-pattern-id . rest)

;; literal-pat ::= bool
;;               | string
;;               | number

;; id-pat      ::= id   ; not match-pattern-id or `...`

;; derived pats will include patterns like
;;               | _
;;               | (var id)
;;               | (? pred-expr)
;;               | (? pred-expr pat)
;;               | (_struct-name pat ...)
;;               | (quote datum)
;;               | (and pat ...)
;;               | (or pat ...)   ; TODO: branches conflict?
;;               | (not pat)
;;               | (list lv-pat ...)

(begin-for-syntax
  (define-values [prop:match-pattern-id
                  match-pattern-id?
                  match-pattern-id-ref]
    (make-struct-type-property 'match-pattern-id))
  (define-syntax-class match-pat-id
    #:attributes [get-get-pat-info]
    [pattern (~var id (local-value match-pattern-id?))
      #:attr get-get-pat-info
      (get-match-pattern-id-function (attribute id.local-value))])
  (define (get-match-pattern-id-function value)
    (cond [(match-pattern-id? value)
           (get-match-pattern-id-function
            ((match-pattern-id-ref value) value))]
          [else value]))

  ;; A PatInfo is a
  ;;   (StxList (StxListof (StxList Id TypeStx))
  ;;            PropStx
  ;;            ExprStx)
  (define-syntax-class pat-info
    #:attributes [[x 1] [τ 1] pos-prop maybe-vec test-concrete?]
    [pattern [([x:id τ:expr] ...) pos-prop maybe-vec test-concrete?]])
  (define-syntax-rule (λ/pat-info v-pat τ-pat obj-pat body ...)
    (λ (v τ obj)
      (syntax-parse (list v τ obj)
        [[v-pat τ-pat obj-pat] body ...])))

  ;; map-app3 : A B C (Listof [A B C -> D]) -> (Listof D)
  (define (map-app3 a b c fs)
    (for/list ([f (in-list fs)])
      (f a b c)))

  (define-syntax-class pat
    #:attributes [get-pat-info]
    ;; get-pat-info : [Stx TypeStx ObjStx -> PatInfo]
    [pattern :derived-pat]
    [pattern :literal-pat]
    [pattern :id-pat])

  (define-syntax-class id-pat
    #:attributes [get-pat-info]
    #:datum-literals [_ ...]
    [pattern (~and x:id (~not (~or :match-pat-id ...)))
      #:attr get-pat-info
      (λ/pat-info v τ o #'[([x τ]) Prop/Top (vector-immutable- v) #t])])

  (define-syntax-class literal-pat
    #:attributes [get-pat-info]
    [pattern b:boolean
      #:attr get-pat-info
      (λ/pat-info v τ o #'[() Prop/Top (if- (eq?- v (quote- b)) #() #f) #f])]
    [pattern s:str
      #:attr get-pat-info
      (λ/pat-info v τ o #'[() Prop/Top (if- (eq?- v (quote- s)) #() #f) #f])]
    [pattern n:number
      #:attr get-pat-info
      (λ/pat-info v τ o #'[() Prop/Top (if- (eq?- v (quote- n)) #() #f) #f])]
    )

  (define-syntax-class derived-pat
    #:attributes [get-pat-info]
    [pattern (~and stx id:match-pat-id)
      #:attr get-pat-info
      (derived-pat->get-info (attribute id.get-get-pat-info) #'stx)]
    [pattern (~and stx (id:match-pat-id . _))
      #:attr get-pat-info
      (derived-pat->get-info (attribute id.get-get-pat-info) #'stx)])

  (define (derived-pat->get-info get-get-pat-info stx)
    (define intro (make-syntax-introducer))
    (define stx* (intro stx))
    (define get-pat-info* (get-get-pat-info stx*))
    (define (get-pat-info v τ o)
      (intro (get-pat-info* v τ o)))
    get-pat-info)
  )

;; ------------------------------------------------------------------------

;; Match

(define-typed-syntax match
  [(_ val:expr [pat:pat body:expr] ...) ≫
   [⊢ val ≫ val- ⇒ τ_val]
   #:with obj (get-arg-obj #'val-)
   #:with tmp (if (identifier? #'val) #'val- (generate-temporary #'val))
   #:with [p:pat-info ...]
   (map-app3 #'tmp #'τ_val #'obj (attribute pat.get-pat-info))
   [[p.x ≫ x- : p.τ] ...
    ⊢ (with-occurrence-prop p.pos-prop body) ≫ body- ⇒ τ_body]
   ...
   #:with τ_out
   (cond [(stx-andmap syntax-e #'[p.test-concrete? ...])
          (cond [(stx-andmap concrete? #'[τ_body ...])
                 #'(CU τ_body ...)]
                [(= 1 (stx-length #'[τ_body ...]))
                 (stx-car #'[τ_body ...])]
                [else
                 #'(U τ_body ...)])]
         [else
          (type-merge* #'[τ_body ...])])
   #:with failure-
   #'(assert- #false (format- "no matching clause for ~v" tmp))
   #:with matching-expr-
   (for/fold ([acc #'failure-])
             ([xs- (in-list (reverse (stx->list #'[[x- ...] ...])))]
              [maybe-vec (in-list (reverse (stx->list #'[p.maybe-vec ...])))]
              [body- (in-list (reverse (stx->list #'[body- ...])))])
     (with-syntax ([acc acc]
                   [v-tmp (generate-temporary)]
                   [maybe-vec maybe-vec]
                   [(x- ...) xs-]
                   [(i- ...) (range (stx-length xs-))]
                   [body- body-])
       (quasisyntax/loc this-syntax
         (let- ([v-tmp maybe-vec])
           #,(syntax/loc this-syntax
               (if- v-tmp
                    (let- ([x- (vector-ref- v-tmp i-)] ...)
                      body-)
                    acc))))))
   --------
   [⊢ (for/all- ([tmp val-]) matching-expr-)
      ⇒ τ_out]])

;; ------------------------------------------------------------------------

;; Match-Pattern Ids

(begin-for-syntax
  (define match-pattern-id
    (local [(struct match-pattern-id [f]
              #:property prop:match-pattern-id
              (λ (this) (match-pattern-id-f this)))]
      match-pattern-id))
  (define macro/match-pattern-id
    (local [(struct macro/match-pattern-id [macro-f match-f]
              #:property prop:procedure
              (struct-field-index macro-f)
              #:property prop:match-pattern-id
              (λ (this) (macro/match-pattern-id-match-f this)))]
      macro/match-pattern-id)))

(define-syntax _
  (match-pattern-id
   (syntax-parser
     [_ (λ/pat-info v τ o #'[() Prop/Top #() #t])])))

(define-syntax var
  (match-pattern-id
   (syntax-parser
     [(_ x:id)
      (λ/pat-info v τ o #'[([x τ]) Prop/Top (vector-immutable- v) #t])])))

;; ------------------------------------------------------------------------

;; Predicate Patterns

(define-syntax ?
  (match-pattern-id
   (syntax-parser
     [(~and
       (_ pred:expr)
       (~⊢ pred ≫ pred- ⇒ : τ_pred))
      (λ/pat-info v τ o
        #:with (~and _
                 (~typecheck
                  [[p? ≫ _ : τ_pred] [x ≫ _ : τ]
                   ⊢ (app* p? x) ≫ _ (⇒ : τ_tst) (⇒ prop+ p+)]))
        #'pred
        #:with c? (concrete? #'τ_tst)
        #'[()
           p+
           (and- (pred- v) #())
           c?])]
     [(~and
       (_ pred:expr p:pat)
       (~⊢ pred ≫ pred- ⇒ : τ_pred))
      (λ/pat-info v τ o
        #:with sub:pat-info
        ((attribute p.get-pat-info) #'v #'τ #'o) ; τ shauld be replaced by p+
        #:with (~and _
                 (~typecheck
                  [[p? ≫ _ : τ_pred] [x ≫ _ : τ]
                   ⊢ (p? x) ≫ _ (⇒ : τ_tst) (⇒ prop+ p+)]))
        #'pred
        #:with c? (and (concrete? #'τ_tst)
                       (syntax-e #'sub.test-concrete?))
        #'[([sub.x sub.τ] ...)
           p+
           (and- (pred- v)
                 sub.maybe-vec)
           c?])])))

;; ------------------------------------------------------------------------

;; Struct Predicate-Accessor Patterns

;; It's on the user to supply a predicate that implies that the accessors
;; won't fail, and will produce values of the given field types.
;; The predicate must also return a concrete boolean when given a concrete
;; argument.

(begin-for-syntax
  (struct struct-predicate-accessor-pattern-id
    [predicate     ; Stx
     accessors     ; [Listof Stx]
     field-types]  ; [Listof TypeStx]
    #:property prop:match-pattern-id
    (λ (this)
      (match-define
        (struct-predicate-accessor-pattern-id predicate
                                              accessors
                                              field-types)
        this)
      (define n (length accessors))
      (unless (= n (length field-types))
        (error 'struct-precidate-accessor-pattern-id
          "must have the same number of accessors and field types"))
      (syntax-parser
        [(s:id sub-pat:pat ...)
         #:fail-unless (= n (stx-length #'[sub-pat ...]))
         (format "expected ~v sub-patterns" n)
         (λ/pat-info v τ o
           #:do [(define τ-concrete? (concrete? #'τ))]
           #:with [sub:pat-info ...]
           (for/list ([get-pat-info (in-list (attribute sub-pat.get-pat-info))]
                      [accessor (in-list accessors)]
                      [field-type (in-list field-types)])
             (get-pat-info #`(#,accessor v)
                           (if τ-concrete?
                               field-type
                               (type-merge field-type field-type))
                           #f))
           #:with c? (and τ-concrete?
                          (stx-andmap syntax-e #'[sub.test-concrete? ...]))
           #`[([sub.x sub.τ] ... ...)
              (Prop/And (Prop/ObjType o : (Struct s #,@field-types))
                        sub.pos-prop
                        ...)
              (and- (#,predicate v)
                    (maybe-vector-append- sub.maybe-vec ...))
              c?])])))
  )

;; ------------------------------------------------------------------------

;; Other Match Forms

(define-typed-syntax match-let
  [(_ ([pat:pat e:expr] ...) body:expr) ≫
   [⊢ [e ≫ e- ⇒ τ_e] ...]
   #:with [tmp ...] (generate-temporaries #'[e ...])
   #:with [v-tmp ...] (generate-temporaries #'[pat ...])
   #:with [p:pat-info ...]
   (for/list ([get-pat-info (in-list (attribute pat.get-pat-info))]
              [v (in-list (stx->list #'[tmp ...]))]
              [τ_e (in-list (stx->list #'[τ_e ...]))]
              [o_e (in-list (stx-map get-arg-obj #'[e- ...]))])
     (get-pat-info v τ_e o_e))
   #:do [(define flat2-lens (stx-flatten/depth-lens 2))]
   #:with [x ...] (lens-view flat2-lens #'[[p.x ...] ...])
   #:with [τ_x ...] (lens-view flat2-lens #'[[p.τ ...] ...])
   [[x ≫ x-- : τ_x] ...
    ⊢ (with-occurrence-prop (Prop/And (Prop p.pos-prop) ...) body) ≫ body-
    ⇒ τ_body]
   #:with [[x- ...] ...] (lens-set flat2-lens #'[[p.x ...] ...] #'[x-- ...])
   #:with [[val_x- ...] ...]
   (for/list ([n (in-list (stx-map stx-length #'[[p.x ...] ...]))]
              [v-tmp (in-list (stx->list #'[v-tmp ...]))])
     (for/list ([i (in-range n)])
       #`(vector-ref- #,v-tmp '#,i)))
   --------
   [⊢ (let- ([tmp e-] ...)
        (let- ([v-tmp p.maybe-vec] ...)
          (assert- v-tmp "match-let pattern failed")
          ...
          (let- ([x- val_x-] ... ...)
            body-)))
      ⇒ τ_body]])

;; ------------------------------------------------------------------------

;; Helpers

(define (maybe-vector-append- . vs)
  (if- (andmap- vector?- vs)
       (apply- vector-append- vs)
       #false))

;; ------------------------------------------------------------------------

