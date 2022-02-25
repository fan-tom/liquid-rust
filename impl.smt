(declare-const x Int)
(declare-const y Int)
(assert (or (and (> x 5) (= y 10)) (and (not (> x 5)) (= y 20))))
(declare-const z Int)
(assert (or (and (> x 5) (= z (+ y 1))) (and (not (> x 5)) (= z (- y 1)))))
(define-fun s () Bool (or (= z 11) (= z 19)))
; if we cannot proof negation of predicate, 
; then we proof that predicate is always true
(assert (not s))
(check-sat)
(get-model)