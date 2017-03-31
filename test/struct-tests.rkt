#lang typed/rosette
(require typed/lib/roseunit)

;; no fields
(struct nofields ())
(check-type nofields : (C→ (Nofields)))
(check-type nofields : (C→ (CNofields)))

;; mutable fields
(struct mut ([x : CSymbol] [y : CBool] [z : CInt #:mutable]))

(define-type-alias CM (CMut CSymbol CBool Int))
(define-type-alias M (U CM))

(check-type mut : (C→ CSymbol CBool Int M))
(check-type mut : (C→ CSymbol CBool Int CM))

(define m (mut 'x #f 1))

(check-type m : CM)

(check-type (mut-x m) : CSymbol -> 'x)
(check-type (mut-y m) : CBool -> #f)
(check-type (mut-z m) : Int -> 1)
;; mutable fields must have possibly-symbolic type
(check-not-type (mut-z m) : CInt)

(set-mut-z! m 2)

(check-type (mut-z m) : Int -> 2)

(typecheck-fail (set-mut-y! m #t)
                #:with-msg "set-mut-y!: unbound identifier")

;; all mutable fields
(struct mut2 ([x : CSymbol] [y : CBool] [z : CInt]) #:mutable)

(define-type-alias Symbol (U CSymbol))
(define-type-alias CM2 (CMut2 Symbol Bool Int))
(define-type-alias M2 (U CM2))

(check-type mut2 : (C→ Symbol Bool Int M2))
(check-type mut2 : (C→ Symbol Bool Int CM2))

(define m2 (mut2 'x #f 1))

(check-type m2 : CM2)

(check-type (mut2-x m2) : Symbol -> 'x)
(check-type (mut2-y m2) : Bool -> #f)
(check-type (mut2-z m2) : Int -> 1)
;; mutable fields must have possibly-symbolic type
(check-not-type (mut2-x m2) : CSymbol)
(check-not-type (mut2-y m2) : CBool)
(check-not-type (mut2-z m2) : CInt)

(set-mut2-x! m2 'y)
(set-mut2-y! m2 #t)
(set-mut2-z! m2 2)

(check-type (mut2-x m2) : Symbol -> 'y)
(check-type (mut2-y m2) : Bool -> #t)
(check-type (mut2-z m2) : Int -> 2)

;; test struct-info (super structs currently only work in untyped code)
(struct a ([x : CInt]))
(provide a)
