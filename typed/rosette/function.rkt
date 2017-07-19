#lang turnstile

(provide partial partialr)

(require typed/rosette/types
         (prefix-in ro: rosette))

;; ----------------------------------------------------------------------------

;; Functions

;; partial* : [A ... B ... -> C] A ... -> [B ... -> C]
(ro:define ((partial* f . as) . bs)
  (ro:apply f (ro:append as bs)))

;; partialr* : [A ... B ... -> C] B ... -> [A ... -> C]
(ro:define ((partialr* f . bs) . as)
  (ro:apply f (ro:append as bs)))

(define-typed-syntax partial
  [(_ f:expr a:expr ...) ≫
   [⊢ f ≫ f- ⇒ : (~C→ τ_ab ... τ_c)]
   #:do [(define na (stx-length #'[a ...]))
         (define-values [τs_a τs_b]
           (split-at (stx->list #'[τ_ab ...]) na))]
   #:with [τ_a ...] τs_a
   #:with [τ_b ...] τs_b
   [⊢ [a ≫ a- ⇐ : τ_a] ...]
   --------
   [⊢ (partial* f- a- ...) ⇒ : (C→ τ_b ... τ_c)]]
  [(_ f:expr a:expr ...) ≫
   [⊢ f ≫ f- ⇒ : (~Ccase-> τ_f ...)]
   [⊢ [a ≫ a- ⇒ : τ_a*] ...]
   #:do [(define na (stx-length #'[a ...]))
         (define results
           (filter
            list?
            (for/list ([τ_f (in-list (stx->list #'[τ_f ...]))])
              (define/syntax-parse (~C→ τ_ab ... τ_c) τ_f)
              (define-values [τs_a τs_b]
                (split-at (stx->list #'[τ_ab ...]) na))
              (and (typechecks? #'[τ_a* ...] τs_a)
                   (list τs_b #'τ_c)))))]
   #:fail-when (empty? results) "no cases match"
   #:with [([τ_b ...] τ_c) ...] results
   --------
   [⊢ (partial* f- a- ...) ⇒ : (Ccase-> (C→ τ_b ... τ_c)
                                         ...)]])

(define-typed-syntax partialr
  [(_ f:expr b:expr ...) ≫
   [⊢ f ≫ f- ⇒ : (~C→ τ_ab ... τ_c)]
   #:do [(define na (- (stx-length #'[τ_ab ...]) (stx-length #'[b ...])))
         (define-values [τs_a τs_b]
           (split-at (stx->list #'[τ_ab ...]) na))]
   #:with [τ_a ...] τs_a
   #:with [τ_b ...] τs_b
   [⊢ [b ≫ b- ⇐ : τ_b] ...]
   --------
   [⊢ (partialr* f- b- ...) ⇒ : (C→ τ_a ... τ_c)]]
  [(_ f:expr b:expr ...) ≫
   [⊢ f ≫ f- ⇒ : (~Ccase-> τ_f ...)]
   [⊢ [b ≫ b- ⇒ : τ_b*] ...]
   #:do [(define nb (stx-length #'[b ...]))
         (define results
           (filter
            syntax?
            (for/list ([τ_f (in-list (stx->list #'[τ_f ...]))])
              (syntax-parse τ_f
                [(~C→ τ_ab ... τ_c)
                 (define na (- (stx-length #'[τ_ab ...]) nb))
                 (define-values [τs_a τs_b]
                   (split-at (stx->list #'[τ_ab ...]) na))
                 (and (typechecks? #'[τ_b* ...] τs_b)
                      #`(C→ #,@τs_a τ_c))]
                [(~C→/conc τ_ab ... τ_c)
                 (define na (- (stx-length #'[τ_ab ...]) nb))
                 (define-values [τs_a τs_b]
                   (split-at (stx->list #'[τ_ab ...]) na))
                 (and (typechecks? #'[τ_b* ...] τs_b)
                      #`(C→/conc #,@τs_a τ_c))]))))]
   #:fail-when (empty? results) "no cases match"
   #:with [τ_a->c ...] results
   --------
   [⊢ (partialr* f- b- ...) ⇒ : (Ccase-> τ_a->c ...)]])

;; ----------------------------------------------------------------------------

