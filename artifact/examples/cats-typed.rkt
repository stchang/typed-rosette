#lang typed/rosette
(require ocelot)

(define univ (node/expr/constant 1 'univ))
(define Un (universe '(a b c d))) ; declare universe of atoms
(define cats (declare-relation 1 "cats")) ; declare a ”cats” relation
(define iCats
  (instantiate-bounds ; create an interpretation for ”cats”
   (bounds Un (list (make-upper-bound cats '((a) (b) (c) (d)))))))

; find an interesting model for ”cats”
(define F (&& (some cats) (some (- univ cats))))

(define resultCats (solve (assert (interpret* F iCats))))

;; Lift the model back to atoms in Un
(interpretation->relations (evaluate iCats resultCats)) ; => cats: b

;; accidentally forget to call evaluate, passing in symbolic vals
;; raises type err instead of failing silently with wrong answer
(interpretation->relations iCats)
