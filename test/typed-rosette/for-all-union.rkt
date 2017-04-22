#lang typed/rosette

(require turnstile/rackunit-typechecking)

(define-symbolic b boolean?)
(define-symbolic x real?)

;; Test from issue #12
(: expect-concrete : (C→ CPosInt CPosInt))
(define (expect-concrete x) x)

(typecheck-fail
 (λ ([x : PosInt])
   (for/all ([y x])
     (expect-concrete y)))
 #:with-msg
 "expected: *CPosInt\n *given: *\\(Term CPosInt\\)\n *expressions: *y")

(check-type
 (λ ([x : PosInt])
   (for/all ([y x])
     (ann y : (Term CPosInt))))
 : (C→ PosInt PosInt))

(check-type
 (λ ([x : (U CInt)])
   (for/all ([y x])
     (ann y : CInt)))
 : (C→ (U CInt) (Term CInt)))

(check-type
 (λ ([x : (U CInt CBool)])
   (for/all ([y x])
     (ann y : (CU CInt CBool))))
 : (C→ (U CInt CBool) (U Int Bool)))

;; ------------------------------------------------------------------------

(define (c-true) -> CTrue #true)
(define (c-false) -> CFalse #false)
(define (c-bool) -> CBool #false)

(define (c-nat) -> CNat 0)
(define (c-int) -> CInt 0)
(define (c-num) -> CNum 0)

(define (c-bv) -> CBV (bv 0 1))
(define (c-str) -> CString "")

(define (u-c-bool-c-nat) -> (U CBool CNat) 0)
(define (u-c-bool-c-str) -> (U CBool CString) "")
(define (u-c-false-c-nat) -> (U CFalse CNat) 0)
(define (u-c-false-c-str) -> (U CFalse CString) "")

(define (cu-c-bool-c-nat) -> (CU CBool CNat) 0)
(define (cu-c-bool-c-str) -> (CU CBool CString) "")
(define (cu-c-false-c-nat) -> (CU CFalse CNat) 0)
(define (cu-c-false-c-str) -> (CU CFalse CString) "")

;; Tests for merging singletons, the only cases where it
;; doesn't produce a U or Term type, because
;; ∀a:τ.∀b:τ.(rkt:eq? a b)

(check-type (if b #true #true) : CTrue)
(check-type (if b #false #false) : CFalse)
(check-type (if b (c-true) #true) : CTrue)
(check-type (if b #false (c-false)) : CFalse)
(check-type (if b (c-true) (c-true)) : CTrue)
(check-type (if b (c-false) (c-false)) : CFalse)

;; Tests for when merging is known to produce a Term

(check-type (if b #true #false) : (Term CBool))
(check-type (if b #false #true) : (Term CBool))
(check-type (if b (c-bool) (c-bool)) : (Term CBool))

(check-type (if b 1 2) : (Term CPosInt))
(check-type (if b 0 2) : (Term CNat))
(check-type (if b -1 1) : (Term (CU CNegInt CPosInt)))
(check-type (if b -1 (if b 0 1)) : (Term CInt))
(check-type (if b -1 (c-nat)) : (Term CInt))
(check-type (if b 1 (c-nat)) : (Term CNat))
(check-type (if b (c-int) (c-nat)) : (Term CInt))

;; Tests for when merging has to produce a U and a Term

(check-type (if b 3.0 3.14) : (U (Term CNum)))
(check-type (if b 3.1 3.14) : (U (Term CNum)))
(check-not-type (if b 3.0 3.14) : (Term CNum))
(check-not-type (if b 3.1 3.14) : (Term CNum))
(check-not-type (if b 3.0 3.14) : (U CNum))
(check-not-type (if b 3.1 3.14) : (U CNum))

(check-type (if b 3.0 x) : (U (Term CNum)))
(check-type (if b 3.1 x) : (U (Term CNum)))
(check-not-type (if b 3.0 x) : (Term CNum))
(check-not-type (if b 3.1 x) : (Term CNum))
(check-not-type (if b 3.0 x) : (U CNum))
(check-not-type (if b 3.1 x) : (U CNum))

(check-type (if b (c-num) (c-num)) : (U (Term CNum)))
(check-not-type (if b (c-num) (c-num)) : (Term CNum))
(check-not-type (if b (c-num) (c-num)) : (U CNum))

(check-type (if b (bv 0 1) (bv 1 1)) : (U (Term CBV)))
(check-type (if b (bv 0 1) (bv 0 2)) : (U (Term CBV)))

(check-type (if b (c-bv) (c-bv)) : (U (Term CBV)))
(check-not-type (if b (c-bv) (c-bv)) : (Term CBV))
(check-not-type (if b (c-bv) (c-bv)) : (U CBV))

;; Tests for when merging produces a U and not a Term

(check-type (if b 2 #true) : (U CPosInt CTrue))
(check-type (if b 2 #true) : (U CPosInt CTrue))
(check-type (if b (c-nat) (c-bool)) : (U CNat CBool))
(check-type (if b (c-nat) (c-str)) : (U CNat CString))

(check-type (if b (c-str) (c-str)) : (U CString))

(check-type (if b (list 1 2) (list 3 4 5))
            : (U (CList CPosInt CPosInt)
                 (CList CPosInt CPosInt CPosInt)))

;; Tests for merging within lists

(check-type (if b (list 1 2) (list 3 4))
            : (CList (Term CPosInt) (Term CPosInt)))

(check-type (if b (list 1 2) (list #true 4))
            : (CList (U CPosInt CTrue) (Term CPosInt)))

(check-type (if b (list (c-bv) (c-str)) (list (c-bv) (c-str)))
            : (CList (U (Term CBV)) (U CString)))

;; Tests for merging unions

(check-type (if b (u-c-bool-c-nat) (u-c-bool-c-str))
            : (U (Term CBool) CNat CString))
(check-not-type (if b (u-c-bool-c-nat) (u-c-bool-c-str))
                : (U CBool CNat CString))

(check-type (if b (cu-c-bool-c-nat) (cu-c-bool-c-str))
            : (U (Term CBool) CNat CString))
(check-not-type (if b (cu-c-bool-c-nat) (cu-c-bool-c-str))
                : (U CBool CNat CString))

;; Merging unions with singletons inside them
(check-type (if b (u-c-false-c-nat) (u-c-false-c-str))
            : (U CFalse CNat CString))
(check-type (if b (cu-c-false-c-nat) (cu-c-false-c-str))
            : (U CFalse CNat CString))

