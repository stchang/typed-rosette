#lang turnstile

(provide ~v format fprintf printf error)

(require typed/rosette/types
         (only-in typed/rosette/base-forms define)
         typed/rosette/unsafe
         (prefix-in ro: rosette))

;; ----------------------------------------------------------------------------

;; Formatting values as strings

(begin-for-syntax
  ;; format-string-matches? : String [Listof Any] -> Bool
  (define (format-string-matches? fmt vals)
    (with-handlers ([exn:fail? (λ (e) #false)])
      (apply format fmt vals)
      #true))
  )

(define ~v (unsafe-assign-type ro:~v : (C→ Any CString)))

(define-typed-syntax format
  [(_ fmt:str v:expr ...) ≫
   #:fail-unless
   (format-string-matches? (syntax-e #'fmt) (syntax->datum #'[v ...]))
   "wrong number of arguments for format string"
   [⊢ [v ≫ v- ⇐ Any] ...]
   --------
   [⊢ (ro:format fmt v- ...) ⇒ CString]])

(define-typed-syntax fprintf
  [(_ out:expr fmt:str v:expr ...) ≫
   [⊢ out ≫ out- ⇐ COutputPort]
   #:fail-unless
   (format-string-matches? (syntax-e #'fmt) (syntax->datum #'[v ...]))
   "wrong number of arguments for format string"
   [⊢ [v ≫ v- ⇐ Any] ...]
   --------
   [⊢ (ro:fprintf out- fmt v- ...) ⇒ CUnit]])

(define-typed-syntax printf
  [(_ fmt:str v:expr ...) ≫
   #:fail-unless
   (format-string-matches? (syntax-e #'fmt) (syntax->datum #'[v ...]))
   "wrong number of arguments for format string"
   [⊢ [v ≫ v- ⇐ Any] ...]
   --------
   [⊢ (ro:printf fmt v- ...) ⇒ CUnit]])

(define-typed-syntax error
  [(_ fmt:expr v:expr ...) ≫
   [⊢ fmt ≫ fmt- ⇐ CString]
   [⊢ [v ≫ v- ⇐ Any] ...]
   --------
   [⊢ (ro:error fmt v- ...) ⇒ CNothing]]
  [(_ sym:expr fmt:str v:expr ...) ≫
   [⊢ sym ≫ sym- ⇐ CSymbol]
   #:fail-unless
   (format-string-matches? (syntax-e #'fmt) (syntax->datum #'[v ...]))
   "wrong number of arguments for format string"
   [⊢ [v ≫ v- ⇐ Any] ...]
   --------
   [⊢ (ro:error sym- fmt v- ...) ⇒ CNothing]])

;; ----------------------------------------------------------------------------

