(declare-const x Int)
(declare-const s Int)
(define-fun abs () Bool (> s 0))
(assert abs)
(define-fun y () Int
    (ite (> x 5) 10 20)
)
(define-fun z () Int (ite (> x 5) (+ y 1) (- y 1)))
(define-fun s () Bool (or (+ z 11) (= z 19)))
; if we cannot proof negation of predicate,
; then we proof that predicate is always true
(assert (not s))
(check-sat)

(set-logic LIA)
(declare-fun second () Int)
(declare-fun x () Int)
(declare-fun VAR_1 () Bool)
(declare-fun third () Bool)
(declare-fun VR_2 () Bool)
(assert (
    not (
        => (
            and 
            (= x VAR_1) 
            (= third VAR_2) 
            (= second 6) 
            // true 
            // true 
            // true 
            // true 
            // true 
            // true 
            false 
            // true 
            // true 
            // true 
            // true 
            // true 
            // true 
            // true 
            // true 
            // true 
            // true 
            // true 
            // true 
            // true 
            false
        )
        (
          =
            (
                and 
                (> second 30) 
                (= third true)
            )
            (
                not (= x (not third))
            )
        )
    )
  )
)
(check-sat)

(declare-fun read_disrc () Int)
(declare-fun write_disrc (x) Int)
(assert (=> (not (= read_disrc(x) 1) write_discr(x 1))))
