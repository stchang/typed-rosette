#lang turnstile

(provide quote
         and or not
         list pair)

(require (postfix-in - rosette)
         "types.rkt"
         (only-in "base-forms.rkt"
           [#%app app*] [list list*])
         (only-in "bool.rkt"
           [and and*] [or or*] [not not*])
         (only-in "list.rkt"
           [pair pair*])
         (only-in "forms-pre-match.rkt"
           [quote quote*])
         "match-core.rkt")

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
;;               | (quote datum)
;;               | (and pat ...)
;;               | (or pat ...)   ; TODO: branches conflict?
;;               | (not pat)
;;               | (list lv-pat ...)

;; ------------------------------------------------------------------------

;; Match-Pattern Ids

(define-syntax quote
  (macro/match-pattern-id
   (syntax-parser
     [(_ datum) #'(quote* datum)])
   (syntax-parser
     [(_ datum)
      (λ/pat-info v τ o
        #:with c? (concrete? #'τ)
        #'[() Prop/Top (if- (eq?- v (quote- datum)) #() #f) c?])])))

(define-syntax and
  (macro/match-pattern-id
   (syntax-parser
     [(_ e:expr ...) #'(and* e ...)])
   (syntax-parser
     [(_ p:pat ...)
      (λ/pat-info v τ o
        #:with [sub:pat-info ...]
        (map-app3 #'v #'τ #'o (attribute p.get-pat-info))
        #:with c? (stx-andmap syntax-e #'[sub.test-concrete? ...])
        #'[([sub.x sub.τ] ... ...)
           Prop/Top
           (maybe-vector-append- sub.maybe-vec ...)
           c?])])))

(define-syntax or
  (macro/match-pattern-id
   (syntax-parser
     [(_ e:expr ...) #'(or* e ...)])
   (syntax-parser
     [(_ p:pat ...)
      (λ/pat-info v τ o
        #:with [sub:pat-info ...]
        (map-app3 #'v #'τ #'o (attribute p.get-pat-info))
        #:with c? (stx-andmap syntax-e #'[sub.test-concrete? ...])
        #'[()
           Prop/Top
           (if- (or- sub.maybe-vec ...) #() #f)
           c?])])))

(define-syntax not
  (macro/match-pattern-id
   (syntax-parser
     [:id #'not*]
     [(_ e:expr) #'(not* e)])
   (syntax-parser
     [(_ p:pat)
      (λ/pat-info v τ o
        #:with sub:pat-info ((attribute p.get-pat-info) #'v #'τ #'o)
        #:with c? #'sub.test-concrete?
        #'[() Prop/Top (if- (not- sub.maybe-vec) #() #f) c?])])))

;; ------------------------------------------------------------------------

;; Helpers

(define (maybe-vector-append- . vs)
  (if- (andmap- vector?- vs)
       (apply- vector-append- vs)
       #false))

;; ------------------------------------------------------------------------

;; List Patterns

;; list-pat    ::= (list lv-pat ...)
;;               | (list* lv-pat ... pat)

;; lv-pat      ::= eh-pat ooo
;;               | pat

;; eh-pat      ::= pat      ; TODO: EH-or patterns?

;; ooo         ::= ...

;; TODO: implement lv-pats and ellipses

(define-syntax list
  (macro/match-pattern-id
   (syntax-parser
     [(_ e:expr ...) #'(list* e ...)])
   (syntax-parser
     [(_ p:pat ...)
      (define n (stx-length #'[p ...]))
      (λ/pat-info v τ o
        (syntax-parse #'τ
          [(~CList τ_elem ...)
           #:when (stx-length=? #'[τ_elem ...] #'[p ...])
           #:with [sub:pat-info ...]
           (for/list ([get-pat-info (attribute p.get-pat-info)]
                      [τ_elem (in-list (stx->list #'[τ_elem ...]))]
                      [i (in-range n)])
             (get-pat-info #`(list-ref- v #,i) τ_elem #f))
           #:with c? (stx-andmap syntax-e #'[sub.test-concrete? ...])
           #'[([sub.x sub.τ] ... ...)
              Prop/Top
              (maybe-vector-append- sub.maybe-vec ...)
              c?]]
          [_
           #:with [sub:pat-info ...]
           (for/list ([get-pat-info (in-list (attribute p.get-pat-info))]
                      [i (in-range n)])
             (get-pat-info #`(list-ref- v #,i) #'Any #f))
           #`[([sub.x sub.τ] ... ...)
              Prop/Top
              (and- (list?- v)
                    (=- #,n (length- v))
                    (maybe-vector-append- sub.maybe-vec ...))
              #f]]))])))

(define-syntax pair
  (macro/match-pattern-id
   (syntax-parser
     [(_ e1:expr e2:expr) #'(pair* e1 e2)])
   (syntax-parser
     [(_ p1:pat p2:pat)
      (λ/pat-info v τ o
        (syntax-parse #'τ
          [(~CPair τ1 τ2)
           #:with s1:pat-info ((attribute p1.get-pat-info) #'(car- v) #'τ1 #f)
           #:with s2:pat-info ((attribute p2.get-pat-info) #'(cdr- v) #'τ2 #f)
           #:with c? (and (attribute s1.test-concrete?)
                          (attribute s2.test-concrete?))
           #'[([s1.x s1.τ] ... [s2.x s2.τ] ...)
              Prop/Top
              (maybe-vector-append- s1.maybe-vec s2.maybe-vec)
              c?]]
          [_
           #:with s1:pat-info ((attribute p1.get-pat-info) #'(car- v) #'Any #f)
           #:with s2:pat-info ((attribute p2.get-pat-info) #'(cdr- v) #'Any #f)
           #`[([s1.x s1.τ] ... [s2.x s2.τ] ...)
              Prop/Top
              (and- (pair?- v)
                    (maybe-vector-append- s1.maybe-vec s2.maybe-vec))
              #f]]))])))

;; ------------------------------------------------------------------------

