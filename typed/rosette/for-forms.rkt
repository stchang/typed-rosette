#lang turnstile

(provide for/fold for for/list for/and for/or
         for*/list
         in-list in-naturals in-range in-set in-vector)

(require typed/rosette/types
         (except-in typed/rosette/base-forms #%app)
         (prefix-in ro: rosette))

;; ----------------------------------------------------------------------------

;; Syntax Classes for For Clauses

;; NOTE:
;;   Rosette's for forms are unlifted, so these for syntax clases require
;;   concrete sequence types and guard types.

(begin-for-syntax
  (define-splicing-syntax-class (for-clause-group env)
    #:attributes [[clause- 1] [env.x 1] [env.τ 1]]
    [pattern (~seq (~var clause (for-clause env))
                   ...)
      #:with [clause- ...] #'[clause.clause- ... ...]
      #:with [[env.x env.τ] ...] #'[[clause.env.x clause.env.τ] ... ...]])

  (define-splicing-syntax-class (guard-clause env)
    #:attributes [[clause- 1]]
    [pattern (~and (~seq #:when bool:expr)
                   (~typecheck
                    #:with [[x τ_x] ...] env
                    [[x ≫ x- : τ_x] ... ⊢ bool ≫ bool- ⇐ CBool]))
      #:with [clause- ...] #`[#:when (let- ([x- x] ...) bool-)]]
    [pattern (~and (~seq #:unless bool:expr)
                   (~typecheck
                    #:with [[x τ_x] ...] env
                    [[x ≫ x- : τ_x] ... ⊢ bool ≫ bool- ⇐ CBool]))
      #:with [clause- ...] #`[#:unless (let- ([x- x] ...) bool-)]]
    [pattern (~and (~seq #:break bool:expr)
                   (~typecheck
                    #:with [[x τ_x] ...] env
                    [[x ≫ x- : τ_x] ... ⊢ bool ≫ bool- ⇐ CBool]))
      #:with [clause- ...] #`[#:break (let- ([x- x] ...) bool-)]]
    [pattern (~and (~seq #:final bool:expr)
                   (~typecheck
                    #:with [[x τ_x] ...] env
                    [[x ≫ x- : τ_x] ... ⊢ bool ≫ bool- ⇐ CBool]))
      #:with [clause- ...] #`[#:final (let- ([x- x] ...) bool-)]])

  (define-splicing-syntax-class (for-clause env)
    #:attributes [[clause- 1] [env.x 1] [env.τ 1]]
    [pattern (~and [x:id seq:expr]
                   (~typecheck
                    #:with [[y τ_y] ...] env
                    [[y ≫ y- : τ_y] ... ⊢ seq ≫ seq- ⇒ (~CSequenceof τ_x)]))
      #:with [clause- ...] #'[[x (let- ([y- y] ...) seq-)]]
      #:with [[env.x env.τ] ...] #'[[x τ_x]]])

  (define-syntax-class (for-clauses env)
    #:attributes [[clause- 1] [env.x 1] [env.τ 1]]
    [pattern ((~var group (for-clause-group env)))
      #:with [clause- ...] #'[group.clause- ...]
      #:with [[env.x env.τ] ...] #'[[group.env.x group.env.τ] ...]]
    [pattern ((~var fst (for-clause-group env))
              (~var guard (guard-clause (stx-append env #'[[fst.env.x fst.env.τ] ...])))
              .
              (~var rst (for-clauses (stx-append env #'[[fst.env.x fst.env.τ] ...]))))
      #:with [clause- ...] #'[fst.clause- ... guard.clause- ... rst.clause- ...]
      #:with [[env.x env.τ] ...] #'[[fst.env.x fst.env.τ] ... [rst.env.x rst.env.τ] ...]]))

;; ----------------------------------------------------------------------------

;; For Loops

(define-typed-syntax for/fold
  [(_ ([acc:id e_init:expr])
      (~var clauses (for-clauses #'[]))
     body:expr ...+) ⇐ τ_acc ≫
   [⊢ e_init ≫ e_init- ⇐ τ_acc]
   [[acc ≫ acc- : τ_acc] [clauses.env.x ≫ x- : clauses.env.τ] ...
    ⊢ (begin body ...) ≫ body- ⇐ τ_acc]
   --------
   [⊢ (ro:for/fold ([acc- e_init-])
                   (clauses.clause- ...)
        (ro:let ([x- clauses.env.x] ...) body-))]]
  [(_ ([acc:id : τ_acc e_init:expr])
      (~var clauses (for-clauses #'[]))
     body:expr ...+) ≫
   [⊢ e_init ≫ e_init- ⇐ τ_acc]
   [[acc ≫ acc- : τ_acc] [clauses.env.x ≫ x- : clauses.env.τ] ...
    ⊢ (begin body ...) ≫ body- ⇐ τ_acc]
   --------
   [⊢ (ro:for/fold ([acc- e_init-])
                   (clauses.clause- ...)
        (ro:let ([x- clauses.env.x] ...) body-))
      ⇒ τ_acc]])

(define-typed-syntax for
  [(_ (~var clauses (for-clauses #'[]))
     body:expr ...+) ≫
   [[clauses.env.x ≫ x- : clauses.env.τ] ...
    ⊢ [body ≫ body- ⇒ _] ...]
   --------
   [⊢ (ro:for (clauses.clause- ...)
        (ro:let ([x- clauses.env.x] ...) body- ...))
      ⇒ CVoid]])

(define-typed-syntax for/list
  [(_ (~var clauses (for-clauses #'[]))
     body:expr ...+) ≫
   [[clauses.env.x ≫ x- : clauses.env.τ] ...
    ⊢ (begin body ...) ≫ body- ⇒ τ_body]
   --------
   [⊢ (ro:for/list (clauses.clause- ...)
        (ro:let ([x- clauses.env.x] ...) body-))
      ⇒ (CListof τ_body)]])

(define-typed-syntax for*/list
  #:datum-literals [:]
  [(_ ([x:id : τ_x:type seq:expr] ...) body:expr) ≫
   #:do [(define (triangle lst)
           (for/list ([i (in-range (stx-length lst))])
             (take (stx->list lst) i)))]
   #:with [[x_prev ...] ...] (triangle #'[x ...])
   #:with [[τ_x_prev ...] ...] (triangle #'[τ_x ...])
   [[x_prev ≫ x_prev- : τ_x_prev] ...
    ⊢ seq ≫ seq- ⇐ (CSequenceof τ_x)]
   ...
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   #:with [[x-_prev ...] ...] (triangle #'[x- ...])
   --------
   [⊢ (ro:for*/list ([x- (let- ([x_prev- x-_prev] ...) seq-)] ...)
        body-)
      ⇒ (CListof τ_body)]])

(define-typed-syntax for/and
  [(_ ([x:id seq:expr] ...) body:expr) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   #:with τ_out (cond [(concrete? #'τ_body) #'(CU CTrue τ_body)]
                      [else (type-merge* #'[CTrue τ_body τ_body])])
   --------
   [⊢ (ro:for/and ([x- seq-] ...) body-)
      ⇒ τ_out]])

(define-typed-syntax for/or
  [(_ ([x:id seq:expr] ...) body:expr) ≫
   [⊢ [seq ≫ seq- ⇒ (~CSequenceof τ_x)] ...]
   [[x ≫ x- : τ_x] ... ⊢ body ≫ body- ⇒ τ_body]
   #:with τ_out (cond [(concrete? #'τ_body) #'(CU CFalse τ_body)]
                      [else (type-merge* #'[CFalse τ_body τ_body])])
   --------
   [⊢ (ro:for/or ([x- seq-] ...) body-)
      ⇒ τ_out]])

;; ----------------------------------------------------------------------------

;; Sequences

(define-typed-syntax in-list
  [(_ e:expr) ≫
   [⊢ e ≫ e- ⇒ : (~CListof ~! τ)]
   --------
   [⊢ (ro:in-list e-) ⇒ : (CSequenceof τ)]]
  [(_ e:expr) ≫
   [⊢ e ≫ e- ⇒ : (~CList ~! τ ...)]
   #:with τ* (cond [(stx-andmap concrete? #'[τ ...])
                    #'(CU τ ...)]
                   [(= 1 (stx-length #'[τ ...]))
                    (stx-car #'[τ ...])]
                   [else
                    #'(U τ ...)])
   --------
   [⊢ (ro:in-list e-) ⇒ : (CSequenceof τ*)]])

(define-typed-syntax in-naturals
  [(_) ≫
   --------
   [⊢ (ro:in-naturals) ⇒ : (CSequenceof CNat)]]
  [(_ e:expr) ≫
   [⊢ e ≫ e- ⇐ CNat]
   --------
   [⊢ (ro:in-naturals e-) ⇒ : (CSequenceof CNat)]])

(define-typed-syntax in-range
  [(_ e:expr) ≫
   [⊢ e ≫ e- ⇐ CNat]
   --------
   [⊢ (ro:in-range e-) ⇒ (CSequenceof CNat)]]
  [(_ a:expr b:expr) ≫
   [⊢ a ≫ a- ⇐ CNat]
   [⊢ b ≫ b- ⇐ CNat]
   --------
   [⊢ (ro:in-range a- b-) ⇒ (CSequenceof CNat)]])

(define-typed-syntax in-set
  [(_ e:expr) ≫
   [⊢ e ≫ e- ⇒ (~or (~CMSetof τ) (~CISetof τ))]
   --------
   [⊢ (ro:in-set e-) ⇒ (CSequenceof τ)]])

(define-typed-syntax in-vector
  [(_ e:expr) ≫
   [⊢ e ≫ e- ⇒ (~or (~CMVectorof τ) (~CIVectorof τ))]
   --------
   [⊢ (ro:in-vector e-) ⇒ (CSequenceof τ)]])

;; ----------------------------------------------------------------------------

