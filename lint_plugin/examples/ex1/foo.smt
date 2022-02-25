(declare-datatypes (T1 T2) ((Pair (mk-pair (first T1) (second T2)))))

(define-fun checked_add ((x (_ BitVec m)) (y (_ BitVec m))) (Pair Bool (_ BitVec m))
  (mk-pair (= #b1 ((_ extract m m) (bvadd ((_ zero_extend 1) x) ((_ zero_extend 1) y)))) (bvadd x y))
)

(declare-fun z () (Pair Bool (_ BitVec 4)))
(declare-fun s () (_ BitVec 4))

(assert (= z (checked_add #b1110 #b0001)))
(assert (= false (first z)))
(assert (= s (second z)))

(check-sat)
(get-model)