#lang turnstile
(require
 (prefix-in t/ro: (only-in "../rosette.rkt" U ~C→ C→))
 (prefix-in ro: rosette/lib/lift))
(provide define-lift)

(define-typed-syntax define-lift
  [(_ x:id [(pred? ...) racket-fn:id]) ≫
   [⊢ [pred? ≫ pred?- ⇒ : (t/ro:~C→ _ ... _)]] ...
   [⊢ [racket-fn ≫ racket-fn- ⇒ : (t/ro:~C→ ty1 ty2)]]
   #:with y (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-syntax- x (make-rename-transformer (assign-type #'y #'(t/ro:C→ (t/ro:U ty1) (t/ro:U ty2)) #:wrap? #f)))
        (ro:define-lift y [(pred?- ...) racket-fn-]))]]
  [(_ x:id [pred? racket-fn:id]) ≫
   [⊢ [pred? ≫ pred?- ⇒ : (t/ro:~C→ _ ... _)]]
   [⊢ [racket-fn ≫ racket-fn- ⇒ : (t/ro:~C→ ty1 ty2)]]
   #:with y (generate-temporary #'x)
   --------
   [≻ (begin-
        (define-syntax- x (make-rename-transformer (assign-type #'y #'(t/ro:C→ (t/ro:U ty1) (t/ro:U ty2)) #:wrap? #f)))
        (ro:define-lift y [pred?- racket-fn-]))]])
