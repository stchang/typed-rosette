#lang typed/rosette

(require turnstile/rackunit-typechecking)

;; These tests make sure that #:when conditions can refer to
;; identifiers defined in previous clauses.

(: string=? : (C→ CString CString CBool))
(define (string=? a b)
  (equal? a b))

(check-type (for/list () 1) : (CListof CInt) -> (list 1))
(check-type (for/list () #t) : (CListof CBool) -> (list #t))
(check-type (for/list () #f) : (CListof CBool) -> (list #f))

(check-type (for/list (#:when #t) 1) : (CListof CInt) -> (list 1))
(check-type (for/list (#:when #f) 1) : (CListof CInt) -> (list))
(check-type (for/list ([x (in-range 5)]) x)
            : (CListof CInt)
            -> (list 0 1 2 3 4))

(check-type (for/list ([s (in-list (list "a" "b" "c"))]
                       [i (in-naturals)])
              (list s i))
            : (CListof (CList CString CInt))
            -> (list (list "a" 0) (list "b" 1) (list "c" 2)))

(check-type (for/list ([s (in-list (list "a" "b" "c"))]
                       [i (in-naturals)]
                       #:when (even? i))
              (list s i))
            : (CListof (CList CString CInt))
            -> (list (list "a" 0) (list "c" 2)))

(check-type (for/list ([s (in-list (list "a" "b" "c" "d" "e"))]
                       [i (in-naturals)]
                       #:when (even? i)
                       [j (in-range i)])
              (list s i j))
            : (CListof (CList CString CInt CInt))
            -> (list (list "c" 2 0)
                     (list "c" 2 1)
                     (list "e" 4 0)
                     (list "e" 4 1)
                     (list "e" 4 2)
                     (list "e" 4 3)))

;; ------------------------------------------------------------------------

;; Test based on section 11 of the racket guide

(check-type (for/list ([book (in-list (list "Guide" "Reference" "Notes"))]
                       #:when (not (string=? book "Notes"))
                       [i (in-naturals 1)]
                       [chapter (in-list (list "Intro" "Details" "Conclusion" "Index"))]
                       #:when (not (string=? chapter "Index")))
              (list book i chapter))
            : (CListof (CList CString CInt CString))
            -> (list (list "Guide" 1 "Intro")
                     (list "Guide" 2 "Details")
                     (list "Guide" 3 "Conclusion")
                     (list "Reference" 1 "Intro")
                     (list "Reference" 2 "Details")
                     (list "Reference" 3 "Conclusion")))

(check-type (for/list ([book (in-list (list "Guide" "Story" "Reference"))]
                       #:break (string=? book "Story")
                       [chapter (in-list (list "Intro" "Details" "Conclusion"))])
              (list book chapter))
            : (CListof (CList CString CString))
            -> (list (list "Guide" "Intro")
                     (list "Guide" "Details")
                     (list "Guide" "Conclusion")))

(check-type (for/list ([book (in-list (list "Guide" "Story" "Reference"))]
                       #:when #true
                       [chapter (in-list (list "Intro" "Details" "Conclusion"))]
                       #:break (and (string=? book "Story")
                                    (string=? chapter "Conclusion")))
              (list book chapter))
            : (CListof (CList CString CString))
            -> (list (list "Guide" "Intro")
                     (list "Guide" "Details")
                     (list "Guide" "Conclusion")
                     (list "Story" "Intro")
                     (list "Story" "Details")))

(check-type (for/list ([book (in-list (list "Guide" "Story" "Reference"))]
                       #:when #true
                       [chapter (in-list (list "Intro" "Details" "Conclusion"))]
                       #:final (and (string=? book "Story")
                                    (string=? chapter "Conclusion")))
              (list book chapter))
            : (CListof (CList CString CString))
            -> (list (list "Guide" "Intro")
                     (list "Guide" "Details")
                     (list "Guide" "Conclusion")
                     (list "Story" "Intro")
                     (list "Story" "Details")
                     (list "Story" "Conclusion")))

(check-type (for/list ([book (in-list (list "Guide" "Story" "Reference"))]
                       #:final (string=? book "Story")
                       [chapter (in-list (list "Intro" "Details" "Conclusion"))])
              (list book chapter))
            : (CListof (CList CString CString))
            -> (list (list "Guide" "Intro")
                     (list "Guide" "Details")
                     (list "Guide" "Conclusion")
                     (list "Story" "Intro")))

;; ------------------------------------------------------------------------

;; Tests based on section 3.18 of the racket reference

(check-type (for/list ([i (in-list (list 1 2 3))]
                       [j (in-list (list "a" "b" "c"))]
                       #:when (odd? i)
                       [k (in-list (list #t #f))])
              (list i j k))
            : (CListof (CList CInt CString CBool))
            -> (list (list 1 "a" #t)
                     (list 1 "a" #f)
                     (list 3 "c" #t)
                     (list 3 "c" #f)))

(check-type (for/list ([i (in-list (list 1 2 3))]
                       [j (in-list (list "a" "b" "c"))]
                       #:break (not (odd? i))
                       [k (in-list (list #t #f))])
              (list i j k))
            : (CListof (CList CInt CString CBool))
            -> (list (list 1 "a" #true)
                     (list 1 "a" #false)))

(check-type (for/list ([i (in-list (list 1 2 3))]
                       [j (in-list (list "a" "b" "c"))]
                       #:final (not (odd? i))
                       [k (in-list (list #t #f))])
              (list i j k))
            : (CListof (CList CInt CString CBool))
            -> (list (list 1 "a" #true)
                     (list 1 "a" #false)
                     (list 2 "b" #true)))

