#lang turnstile

(provide gen:custom-write gen:equal+hash define-generics)

(require "types.rkt"
         "struct.rkt"
         (prefix-in ro: (only-in rosette define-generics)))
(module+ test
  (require turnstile/rackunit-typechecking
           "base-forms.rkt"
           (only-in "forms-pre-match.rkt" quote)
           (only-in "format.rkt" fprintf)))

(define-syntax gen:custom-write
  (generic-interface-type-info
   #'gen:custom-write-
   (λ (τ)
     (list
      (list 'write-proc
            #`(C→ #,τ COutputPort (CU CBool CNat) CVoid))))))

(define-syntax gen:equal+hash
  (generic-interface-type-info
   #'gen:equal+hash-
   (λ (τ)
     (list
      (list 'equal-proc
            #`(C→ #,τ #,τ (C→ Any Any CBool) CBool))
      (list 'hash-proc
            #`(C→ #,τ (C→ Any CInt) CInt))
      (list 'hash2-proc
            #`(C→ #,τ (C→ Any CInt) CInt))))))

;; ----------------------------------------------------------------------------

(begin-for-syntax
  (define-syntax-class ->
    [pattern (~or (~datum →) (~datum ->))])

  (define (method-args-erase args)
    (syntax-parse args
      #:datum-literals [:]
      [([x:id : τ_in] ...) #'(x ...)]
      [([x:id : τ_in] ... . [rst:id : τ_rst]) #'(x ... . rst)]))

  (define (method-args->τ args τ_out)
    (syntax-parse args
      #:datum-literals [:]
      [([x:id : τ_in] ...) #`(C→ τ_in ... #,τ_out)]
      [([x:id : τ_in] ... . [rst:id : τ_rst])
       #`(C→* [τ_in ...] [] #:rest τ_rst #,τ_out)])))

(define-syntax-parser define-generics
  [(_ generic-id:id
     (~or (~seq #:type-name Name:id)
          (~seq (~fail #:unless (id-lower-case? #'generic-id)
                       (format "Expected lowercase generic name, given ~a" #'generic-id))
                (~parse Name:id (id-upcase #'generic-id))))
     [(method-id:id . method-args) :-> method-τ_out]
     ...
     . opt-args)
   #:with gen-generic-id (format-id #'generic-id "gen:~a" #'generic-id)
   #:with [method-args- ...]
   (stx-map method-args-erase #'[method-args ...])
   #:with [method-τ ...]
   (stx-map method-args->τ #'[method-args ...] #'[method-τ_out ...])
   #:do [(define intro (make-syntax-introducer))]
   #:with [generic-id* gen-generic-id* [method-id* ...] [method-args* ...]]
   (intro #'[generic-id gen-generic-id [method-id ...] [method-args- ...]])
   #'(begin-
       (ro:define-generics generic-id*
         (method-id* . method-args*)
         ... . opt-args)
       (define-syntax gen-generic-id
         (generic-interface-type-info
          #'gen-generic-id*
          (λ (τ)
            (with-syntax ([Name τ])
              (list
               (list 'method-id #'method-τ)
               ...)))))
       (define-syntax method-id
         (make-variable-like-transformer
          ; TODO: Define Name as a non-Any type that is a
          ;       supertype of all structs that implement
          ;       this, but not of anything else.
          (with-syntax ([Name #'Any])
            (assign-type #'method-id* #'method-τ))))
       ...)])

;; ----------------------------------------------------------------------------

(module+ test
  (struct foo ([a : Int])
    #:type-name Foo
    #:transparent
    #:methods gen:custom-write
    [(define (write-proc this out mode)
       (fprintf out "~v" (foo-a this)))])

  (define-generics colorable #:type-name Colorable
    [(get-color [colorable : Colorable]) -> String]
    [(set-color [colorable : Colorable] [color : String]) -> Colorable])

  (struct point ([x : Float] [y : Float] [color : String])
    #:type-name Point
    #:transparent
    #:methods gen:colorable
    [(define (get-color self)
       (point-color self))
     (define (set-color self color)
       (point (point-x self) (point-y self) color))])

  (check-type (get-color (point '1.2 '2.4 '"blue")) : String -> '"blue")
  ;; TODO: return Colorable instead of Any
  (check-type (set-color (point '1.2 '2.4 '"blue") '"green") : Any
              -> (point '1.2 '2.4 '"green"))
  )
