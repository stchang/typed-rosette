#lang turnstile

(provide struct
         (for-syntax generic-interface-type-info))

(require racket/splicing
         (prefix-in ro: (only-in rosette/safe struct))
         (only-in racket/private/generic-methods
                  generic-property
                  generic-method-table)
         (only-in turnstile/examples/stlc+union
                  define-named-type-alias)
         typed/rosette/types
         typed/rosette/base-forms
         typed/rosette/forms-pre-match
         typed/rosette/match-core
         typed/rosette/unsafe
         (for-syntax racket/struct-info
                     racket/syntax
                     syntax/parse/class/local-value))
(module+ test
  (require turnstile/rackunit-typechecking))

(begin-for-syntax
  (define (add-pred stx pred)
    (set-stx-prop/preserved stx 'pred pred))
  (define (get-pred stx)
    (syntax-property stx 'pred)))

(define-syntax-parser add-predm
  [(_ stx pred) (add-pred #'stx #'pred)])

;; ----------------------------------------------------------------------------

;; Generic Interfaces

(begin-for-syntax
  (struct generic-interface-type-info [untyped-binding get-methods])
  ;; get-methods : [TypeStx -> (Listof (List Symbol TypeStx))]
  (define-syntax-class generic-interface-id
    #:attributes [id- get-methods]
    [pattern generic-interface
      #:declare generic-interface (local-value generic-interface-type-info?)
      #:do [(match-define (generic-interface-type-info binding methods)
              (attribute generic-interface.local-value))]
      #:with id- binding
      #:attr get-methods methods]))

;; ----------------------------------------------------------------------------

(begin-for-syntax
  (define struct-transformer-binding 'struct-transformer-binding)
  (define struct-instance-type 'struct-instance-type)
  (define struct-accessors 'struct-accessors)
  (define struct-field-types 'struct-field-types)
  (define-syntax-class super
    [pattern super:typed-struct-id
      #:with [accessor ...] #'[super.accessor ...]
      #:with [τ_fld ...] #'[super.τ_fld ...]
      #:with [τ_fld_merged ...] #'[super.τ_fld_merged ...]
      #:attr some-mutable? (attribute super.some-mutable?)
      #:with [id-:id τ_inst]
      (let ([super (local-expand #'super 'expression '())])
        (list (syntax-property super struct-transformer-binding)
              (syntax-property super struct-instance-type)))])

  ;; -----------------------------------
  ;; Struct Options

  (define-splicing-syntax-class struct-options
    #:attributes [get-opts- some-mutable?]
    [pattern (~seq mut:struct-opt-mutability
                   trns:struct-opt-opacity
                   refl:struct-opt-reflection-name
                   stpr:struct-opt-property ...
                   gnrc:struct-opt-generic-methods ...)
      #:attr some-mutable? (attribute mut.mutable?)
      #:attr get-opts-
      (lambda (τ)
        (apply stx-append
               #'[mut.opt- ... trns.opt- ... refl.opt- ... stpr.opt- ... ...]
               (for/list ([get-opts- (in-list (attribute gnrc.get-opts-))])
                 (get-opts- τ))))])

  (define-splicing-syntax-class struct-opt-mutability
    [pattern (~seq)
      #:attr mutable? #false
      #:with [opt- ...] #'[]]
    [pattern (~seq #:mutable)
      #:attr mutable? #true
      #:with [opt- ...] #'[#:mutable]])

  (define-splicing-syntax-class struct-opt-opacity
    [pattern (~seq)
      #:with [opt- ...] #'[]]
    [pattern (~seq #:transparent)
      #:with [opt- ...] #'[#:transparent]])

  (define-splicing-syntax-class struct-opt-reflection-name
    [pattern (~seq)
      #:with [opt- ...] #'[]]
    [pattern (~seq #:reflection-name
                   (~and sym-expr:expr
                         (~⊢ sym-expr ≫ sym-expr- ⇐ CSymbol)))
      #:with [opt- ...] #'[#:reflection-name sym-expr-]])

  (define-splicing-syntax-class struct-opt-property
    #:attributes [[opt- 1]]
    [pattern (~seq #:property
                   (~and prop:expr
                         (~⊢ prop ≫ prop- ⇒ (~CStructTypeProp τ_v)))
                   val)
      #:with [opt- ...] #`[#:property prop- (ann val : τ_v)]])

  (define-splicing-syntax-class struct-opt-generic-methods
    #:attributes [get-opts-]
    [pattern (~seq #:methods gnrc:generic-interface-id [method-def:expr ...])
      #:attr get-opts-
      (λ (τ)
        (define id-
          ((make-syntax-delta-introducer #'gnrc #'gnrc.id-) #'gnrc.id- 'flip))
        (define type-decls
          (for/list ([method/τ (in-list ((attribute gnrc.get-methods) τ))])
            (define method-id
              ;((make-syntax-delta-introducer #'gnrc #'gnrc.id-)
               (datum->syntax #'gnrc (first method/τ) #'gnrc));)
            (define τ_method (second method/τ))
            #`(: #,method-id : #,τ_method)))
        (syntax-parse type-decls
          [(type-decl ...)
           #`[#:property (generic-property #,id-)
              (generic-method-table #,id- #:scope gnrc
                                    type-decl ...
                                    method-def ...)]]))])

  ;; -----------------------------------
  )

(define-syntax-parser struct
  #:datum-literals [:]
  [(_ name:id (field:id ...+) . _)
   (raise-syntax-error #f "Missing type annotations for fields" this-syntax)]
  [(_ name:id ([field:id : τ:type . fld-opts] ...)
      (~or (~seq #:type-name Name:id)
           (~seq (~fail #:unless (id-lower-case? #'name)
                        (format "Expected lowercase struct name, given ~a" #'name))
                 (~parse Name:id (id-upcase #'name))))
      opts:struct-options)
   #:with CName (format-id #'Name "C~a" #'Name #:source #'Name)
   #:with constructor/type (generate-temporary #'name)
   #:with name? (format-id #'name "~a?" #'name #:source #'name)
   #:with [name-field ...]
   (for/list ([field (in-list (syntax->list #'[field ...]))])
     (format-id #'name "~a-~a" #'name field #:source #'name #:props #'name))
   #:with [(set-field! setter-ty) ...]
   (for/list ([field (in-list (syntax->list #'[field ...]))]
              [fopts (in-list (syntax->list #'[fld-opts ...]))]
              [fldty (in-list (syntax->list #'[τ ...]))]
              #:unless (null? (stx->datum fopts)))
     (list
      (format-id #'name "set-~a-~a!" #'name field #:source #'name #:props #'name)
      #`(C→ CName #,fldty CUnit)))
   ;; set-field! must be part of this stx-introducing,
   ;; if it uses a separate mk-stx-intro call, it wont get the right scopes
   #:with [name* internal-name name?* (name-field* ...) (set-field!* ...)]
   ((make-syntax-introducer) #'[name name name? (name-field ...) (set-field! ...)])
   #:with [opt- ...] ((attribute opts.get-opts-) #'CName)
   #:with [τ_merged ...] (stx-map type-merge #'[τ.norm ...] #'[τ.norm ...])
   #:with n (datum->syntax #'here (stx-length #'[field ...]))
   #:with some-mutable? (attribute opts.some-mutable?)
   #'(begin-
       (ro:struct name* [[field . fld-opts] ...] opt- ...)
       (define-struct-name name constructor/type internal-name CName name?
         [name-field ...]
         [τ.norm ...]
         #false
         #true
         some-mutable?)
       (define-named-type-alias CName
         (Struct name τ.norm ...))
       (define-named-type-alias Name
         (add-predm (U (Struct name τ_merged ...)) name?))
       (define-syntax- constructor/type
         (make-variable-like-transformer
          (⊢ name* : (C→ τ.norm ... CName))))
       (: name? : (LiftedPredFor Name))
       (define name?
         (unsafe-assign-type name?* : (LiftedPredFor Name)))
       (: name-field : (Ccase-> (C→ CName τ)
                                (C→ Name τ_merged)))
       ...
       (define name-field
         (unsafe-assign-type name-field* : (Ccase-> (C→ CName τ)
                                                    (C→ Name τ_merged))))
       ...
       (: set-field! : setter-ty #;(Ccase-> (C→ CName τ CUnit)
                               (C→ Name τ_merged CUnit)))
       ...
       (define set-field!
         (unsafe-assign-type set-field!* : setter-ty #;(Ccase-> (C→ CName τ CUnit)
                                                   (C→ Name τ_merged CUnit))))
       ...)]
;;       )]
  ;; Sub-structs
  ;; TODO: Allow defining a new type for the sub-struct that
  ;;       is a distinct subtype of the parent's type.
  [(_ name:id super:super ([field:id : τ:type] ...)
      (~or (~seq #:type-name Name:id)
           (~seq (~fail #:unless (id-lower-case? #'name)
                        (format "Expected lowercase struct name, given ~a" #'name))
                 (~parse Name:id (id-upcase #'name))))
      opts:struct-options)
   #:with CName (format-id #'Name "C~a" #'Name #:source #'Name)
   #:with name? (format-id #'name "~a?" #'name #:source #'name)
   #:with [name-field ...]
   (for/list ([field (in-list (syntax->list #'[field ...]))])
     (format-id #'name "~a-~a" #'name field #:source #'name #:props #'name))
   #:with constructor/type (generate-temporary #'name)
   #:with [name* internal-name name?* name-field* ...]
   ((make-syntax-introducer) #'[name name name? name-field ...])
   #:with [opt- ...] ((attribute opts.get-opts-) #'CName)
   #:with [τ_merged ...] (stx-map type-merge #'[τ.norm ...] #'[τ.norm ...])
   #:with some-mutable? (or (attribute super.some-mutable?)
                            (attribute opts.some-mutable?))
   #'(begin-
       (ro:struct name* super [field ...] opt- ...)
       (define-struct-name name constructor/type internal-name CName name?
         [super.accessor ... name-field ...]
         [super.τ_fld ... τ.norm ...]
         super
         #false
         some-mutable?)
       (define-named-type-alias CName
         (Struct name super.τ_fld ... τ.norm ...))
       (define-named-type-alias Name
         (add-predm (U (Struct name super.τ_fld_merged ... τ_merged ...)) name?))
       (define-syntax- constructor/type
         (make-variable-like-transformer
          (⊢ name* : (C→ super.τ_fld ... τ.norm ... CName))))
       (: name? : LiftedPred)
       (define name?
         (unsafe-assign-type name?* : (LiftedPredFor Name)))
       (: name-field : (Ccase-> (C→ CName τ)
                                (C→ Name τ_merged)))
       ...
       (define name-field
         (unsafe-assign-type name-field* :
                             (Ccase-> (C→ CName τ)
                                      (C→ Name τ_merged))))
       ...)]
  )

(begin-for-syntax
  (struct typed-struct-info/match typed-struct-info []
    #:property prop:match-pattern-id
    (λ (self)
      (struct-predicate-accessor-pattern-id
       (typed-struct-info-predicate self)
       (typed-struct-info-accessors self)
       (typed-struct-info-field-types self))))
  (define (make-typed-struct-info constructor
                                  untyped-id
                                  type
                                  predicate
                                  accessors
                                  field-types
                                  super-id
                                  no-super?
                                  some-mutable?)
    (typed-struct-info/match
     (make-variable-like-transformer
      (set-stx-prop/preserved
       (set-stx-prop/preserved
        (set-stx-prop/preserved
         (set-stx-prop/preserved
          constructor
          struct-transformer-binding
          untyped-id)
         struct-instance-type
         type)
        struct-accessors
        accessors)
       struct-field-types
       field-types))
     untyped-id
     predicate
     accessors
     field-types
     super-id
     no-super?
     some-mutable?)))

(define-syntax-parser define-struct-name
  [(_ name constructor untyped-transformer CName predicate
      [accessor ...]
      [field-type ...]
      (~and super-id (~or :id #false))
      no-super?:boolean
      some-mutable?:boolean)
   #'(begin-
       (define-syntax- name
         (make-typed-struct-info (quote-syntax constructor)
                                 (quote-syntax untyped-transformer)
                                 (quote-syntax CName)
                                 (quote-syntax predicate)
                                 (list (quote-syntax accessor) ...)
                                 (list (quote-syntax field-type) ...)
                                 (and (quote super-id) (quote-syntax super-id))
                                 (quote no-super?)
                                 (quote some-mutable?)))
       )])

;; ----------------------------------------------------------------------------

(module+ test
  (struct a () #:transparent)
  (struct b () #:transparent)
  (struct c () #:transparent)
  (struct d () #:transparent)
  (struct e () #:transparent)
  (struct abc ([a : A] [b : B] [c : C]) #:transparent)

  (check-type (a) : A -> (a))
  (check-type (b) : B -> (b))
  (check-type (c) : C -> (c))
  (check-type (d) : D -> (d))
  (check-type (e) : E -> (e))
  (check-type (abc (a) (b) (c)) : CAbc -> (abc (a) (b) (c)))
  (typecheck-fail (abc (a) '3 (c))
    #:with-msg
    #;"expected B, given PosInt\n *expression: '3"
    "expected: *A, B, C\n *given: *CA, PosInt, CC\n *expressions: \\(a\\), \\(quote 3\\), \\(c\\)")

  ;; predicates
  (check-type (a? (a)) : Bool -> '#true)
  (check-type (a? (b)) : Bool -> '#false)
  (check-type (a? (abc (a) (b) (c))) : Bool -> '#false)
  (check-type (abc? (abc (a) (b) (c))) : Bool -> '#true)

  ;; inheritance
  ;; This defines a new type, CAbcde, which is a subtype of CAbc.
  (struct abcde abc ([d : D] [e : E]) #:transparent)

  (check-type (abcde (a) (b) (c) (d) (e)) : CAbcde
              -> (abcde (a) (b) (c) (d) (e)))
  (check-type (abcde (a) (b) (c) (d) (e)) : CAbc
              -> (abcde (a) (b) (c) (d) (e)))
  (typecheck-fail (abcde (a) (b) (c) '3 (e))
    #:with-msg
    #;"expected D, given PosInt\n *expression: 3"
    "expected: *A, B, C, D, E\n *given: *CA, CB, CC, PosInt, CE\n *expressions: \\(a\\), \\(b\\), \\(c\\), \\(quote 3\\), \\(e\\)")

  ;; inheritance and predicates
  (check-type (abc? (abc (a) (b) (c))) : Bool -> '#true)
  (check-type (abcde? (abcde (a) (b) (c) (d) (e))) : Bool -> '#true)
  (check-type (abc? (abcde (a) (b) (c) (d) (e))) : Bool -> '#true)
  (check-type (a? (abcde (a) (b) (c) (d) (e))) : Bool -> '#false)
  (check-type (abcde? (abc (a) (b) (c))) : Bool -> '#false)
  )
