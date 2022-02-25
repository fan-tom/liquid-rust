; Define predicates for checking if add/sub overflows
; Unsigned add/sub
; 8 bit
(define-fun bvu8add_overflows ((x (_ BitVec 8)) (y (_ BitVec 8))) Bool
  (let (
        (ext_x ((_ zero_extend 1) x))
        (ext_y ((_ zero_extend 1) y))
        )
    (= #b1 ((_ extract 8 8) (bvadd ext_x ext_y)))
    )
  )
; 16 bit
(define-fun bvu16add_overflows ((x (_ BitVec 16)) (y (_ BitVec 16))) Bool
  (let (
        (ext_x ((_ zero_extend 1) x))
        (ext_y ((_ zero_extend 1) y))
        )
    (= #b1 ((_ extract 16 16) (bvadd ext_x ext_y)))
    )
  )
; 32 bit
(define-fun bvu32add_overflows ((x (_ BitVec 32)) (y (_ BitVec 32))) Bool
  (let (
        (ext_x ((_ zero_extend 1) x))
        (ext_y ((_ zero_extend 1) y))
        )
    (= #b1 ((_ extract 32 32) (bvadd ext_x ext_y)))
    )
  )
; 64 bit
(define-fun bvu64add_overflows ((x (_ BitVec 64)) (y (_ BitVec 64))) Bool
  (let (
        (ext_x ((_ zero_extend 1) x))
        (ext_y ((_ zero_extend 1) y))
        )
    (= #b1 ((_ extract 64 64) (bvadd ext_x ext_y)))
    )
  )
; 128 bit
(define-fun bvu128add_overflows ((x (_ BitVec 128)) (y (_ BitVec 128))) Bool
  (let (
        (ext_x ((_ zero_extend 1) x))
        (ext_y ((_ zero_extend 1) y))
        )
    (= #b1 ((_ extract 128 128) (bvadd ext_x ext_y)))
    )
  )
; Sub
; 8 bit
(define-fun bvu8sub-overflows ((x (_ BitVec 8)) (y (_ BitVec 8))) Bool
  (let (
        (ext_x ((_ sign_extend 1) x))
        (ext_y ((_ sign_extend 1) y))
        )
    (= #b1 ((_ extract 8 8) (bvsub ext_x ext_y)))
    )
  )
; Signed
; 8 bit
(define-fun bvs8add_overflows ((x (_ BitVec 8)) (y (_ BitVec 8))) Bool
  (let (
        (ext_x ((_ sign_extend 1) x))
        (ext_y ((_ sign_extend 1) y))
        )
    (= #b1 ((_ extract 8 8) (bvadd ext_x ext_y)))
    )
  )
; 16 bit
(define-fun bvs16add_overflows ((x (_ BitVec 16)) (y (_ BitVec 16))) Bool
  (let (
        (ext_x ((_ sign_extend 1) x))
        (ext_y ((_ sign_extend 1) y))
        )
    (= #b1 ((_ extract 16 16) (bvadd ext_x ext_y)))
    )
  )
; 32 bit
(define-fun bvs32add_overflows ((x (_ BitVec 32)) (y (_ BitVec 32))) Bool
  (let (
        (ext_x ((_ sign_extend 1) x))
        (ext_y ((_ sign_extend 1) y))
        )
    (= #b1 ((_ extract 32 32) (bvadd ext_x ext_y)))
    )
  )
; 64 bit
(define-fun bvs64add_overflows ((x (_ BitVec 64)) (y (_ BitVec 64))) Bool
  (let (
        (ext_x ((_ sign_extend 1) x))
        (ext_y ((_ sign_extend 1) y))
        )
    (= #b1 ((_ extract 64 64) (bvadd ext_x ext_y)))
    )
  )
; 128 bit
(define-fun bvs128add_overflows ((x (_ BitVec 128)) (y (_ BitVec 128))) Bool
  (let (
        (ext_x ((_ sign_extend 1) x))
        (ext_y ((_ sign_extend 1) y))
        )
    (= #b1 ((_ extract 128 128) (bvadd ext_x ext_y)))
    )
  )
; show bitvectors as (_ bv# #) instead of hexadecimal
(set-option :pp.bv-literals false)
(push)
(declare-fun return () (_ BitVec 32))
(declare-fun a () (_ BitVec 32))
(assert (= (bvcomp return a) (_ bv1 1)))
(assert (not (= (bvcomp return a) (_ bv1 1))))
(check-sat)
(pop)
(push)
(declare-fun LOCAL_5__0_14 () (_ BitVec 32))
(declare-fun LOCAL_6__0_14 () (_ BitVec 32))
(declare-fun a () (_ BitVec 32))
(declare-fun LOCAL_3__0_14 () (_ BitVec 32))
(declare-fun LOCAL_4__0_14 () Bool)
(declare-fun x () (_ BitVec 32))
(declare-fun LOCAL_2__0_14 () Bool)
(declare-fun return () (_ BitVec 32))
(assert (= (bvcomp a LOCAL_6__0_14) (_ bv1 1)))
(assert (and (= LOCAL_2__0_14 (bvslt LOCAL_3__0_14 (_ bv0 32))) (= LOCAL_2__0_14 false)))
(assert (= (bvcomp LOCAL_3__0_14 x) (_ bv1 1)))
(assert (= (bvcomp LOCAL_5__0_14 x) (_ bv1 1)))
(assert (= (bvcomp LOCAL_6__0_14 x) (_ bv1 1)))
(assert (and (= LOCAL_4__0_14 (= (bvcomp LOCAL_5__0_14 (_ bv0 32)) (_ bv1 1))) (not (= LOCAL_4__0_14 false))))
(assert (not (= (bvcomp a (_ bv0 32)) (_ bv1 1))))
(check-sat)
(pop)
(push)
(declare-fun return () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(declare-fun LOCAL_5__0_14 () (_ BitVec 32))
(declare-fun LOCAL_6__0_14 () (_ BitVec 32))
(declare-fun LOCAL_3__0_14 () (_ BitVec 32))
(declare-fun LOCAL_4__0_14 () Bool)
(declare-fun LOCAL_2__0_14 () Bool)
(assert (= (bvcomp LOCAL_5__0_14 x) (_ bv1 1)))
(assert (= (bvcomp LOCAL_3__0_14 x) (_ bv1 1)))
(assert (= (bvcomp LOCAL_6__0_14 x) (_ bv1 1)))
(assert (not (and (not (and (= LOCAL_2__0_14 (bvslt LOCAL_3__0_14 (_ bv0 32))) (not (= LOCAL_2__0_14 false)))) (not (and (= LOCAL_2__0_14 (bvslt LOCAL_3__0_14 (_ bv0 32))) (= LOCAL_2__0_14 false))))))
(assert (not (and (not (and (= LOCAL_4__0_14 (= (bvcomp LOCAL_5__0_14 (_ bv0 32)) (_ bv1 1))) (= LOCAL_4__0_14 false))) (not (and (= LOCAL_4__0_14 (= (bvcomp LOCAL_5__0_14 (_ bv0 32)) (_ bv1 1))) (not (= LOCAL_4__0_14 false)))))))
(assert (not (and (not (= (bvcomp return (_ bv1 32)) (_ bv1 1))) (and (not (= (bvcomp return (_ bv2 32)) (_ bv1 1))) (not (= (bvcomp return (bvadd LOCAL_6__0_14 (_ bv1 32))) (_ bv1 1)))))))
(assert (not (bvsgt return (_ bv0 32))))
(check-sat)
(get-model)
(pop)
(push)
(declare-fun VAR_1 () (_ BitVec 32))
(declare-fun LOCAL_2__0_13 () (_ BitVec 32))
(declare-fun return () (_ BitVec 32))
(declare-fun VAR_2 () Bool)
(declare-fun a () (_ BitVec 32))
(assert (= (bvcomp LOCAL_2__0_13 a) (_ bv1 1)))
(assert (= (bvcomp a (_ bv0 32)) (_ bv1 1)))
(assert (= (bvcomp VAR_1 (bvadd LOCAL_2__0_13 (_ bv1 32))) (_ bv1 1)))
(assert (= (bvcomp return VAR_1) (_ bv1 1)))
(assert (and (= VAR_2 (bvs32add_overflows LOCAL_2__0_13 (_ bv1 32))) (= VAR_2 false)))
(assert (not (= (bvcomp return (bvadd a (_ bv1 32))) (_ bv1 1))))
(check-sat)
(pop)
(push)
(declare-fun LOCAL_2__0_12 () (_ BitVec 32))
(declare-fun ret () (_ BitVec 32))
(assert (not true))
(check-sat)
(pop)
(push)
(declare-fun LOCAL_2__0_12 () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(declare-fun ret () (_ BitVec 32))
(assert (= (bvcomp x LOCAL_2__0_12) (_ bv1 1)))
(assert (not true))
(check-sat)
(pop)
(push)
(declare-fun LOCAL_2__0_12 () (_ BitVec 32))
(declare-fun ret () (_ BitVec 32))
(assert (bvsgt ret (_ bv0 32)))
(assert (not true))
(check-sat)
(pop)
