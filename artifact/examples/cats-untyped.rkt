#lang typed/rosette
(require ocelot typed/lib/roseunit)

(define Un (universe '(a b c d))) ; declare universe of atoms
(define cats (declare-relation 1 "cats")) ; declare a ”cats” relation
(define iCats (instantiate-bounds ; create an interpretation for ”cats”
               (bounds Un (list (make-upper-bound cats '((a) (b) (c) (d)))))))
(define F (some cats) )
(- univ cats)
;; (if (some cats)
;;               (some (- cats cats))
;;               #f)) ; find an interesting model for ”cats”
(define resultCats (solve (assert (interpret* (unsafe-cast-nonfalse F) iCats))))

;(evaluate iCats resultCats)
; Lift the model back to atoms in Un
;(interpretation->relations (evaluate iCats resultCats)) ; => cats: b

;; accidentally forget to call evaluate, passing in symbolic vals
;; - should be type err
(interpretation->relations iCats) ; => cats: a,b,c,d (WRONG)
