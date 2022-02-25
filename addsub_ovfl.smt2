(define-fun bvu8add-overflows ((x (_ BitVec 8)) (y (_ BitVec 8))) Bool
  (let (
        (ext_x ((_ zero_extend 1) x))
        (ext_y ((_ zero_extend 1) y))
        )
    (= #b1 ((_ extract 8 8) (bvadd ext_x ext_y)))
    )
  )

(assert (bvu8add-overflows (_ bv7 254) #b00000001))
(check-sat)
