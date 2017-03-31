#lang typed/rosette

(require typed/lib/roseunit)

;; tests for quoting

;; base datums
(check-type '0 : CZero -> 0)
(check-type '1 : CPosInt -> 1)
(check-type '1 : CNat -> 1)
(check-type '1 : Nat -> 1)
(check-type '1 : Int -> 1)
(check-type '-2 : CNegInt -> -2)
(check-type '-2 : CInt -> -2)
(check-type '-2 : Int -> -2)

(check-type 'x : CSymbol -> 'x)

;; pairs
(check-type '(1 . 2) : (CPair CNat CNat) -> (cons 1 2))
(check-type '(1 . x) : (CPair CNat CSymbol) -> (cons 1 'x))
(check-type '(x . 1) : (CPair CSymbol CNat) -> (cons 'x 1))
(check-type '(x . y) : (CPair CSymbol CSymbol) -> (cons 'x 'y))

;; lists
(check-type '() : (CList))
(check-type '() : (CListof Int))
(check-type '() : (CListof CBool))
(check-type '() : (Listof Int))
(check-type '(1 2 3) : (CList CNat CNat CNat) -> (list 1 2 3))
(check-type '(1 2 3) : (CListof CNat) -> (list 1 2 3))
(check-type '(1 2 3) : (CListof Int))

;; nested lists
(define lsts '((1) (2 3) (4 5 6)))
(check-type lsts : (CList (CList CNat) (CList CNat CNat) (CList CNat CNat CNat)))
(check-type lsts : (CList (CListof CNat) (CListof CNat) (CListof CNat)))
(check-type lsts : (CListof (CListof CNat)))

;; assoc lists
(define a '((x . 1) (y . 2) (z . 3)))
(check-type a : (CListof (CPair CSymbol CNat)))
