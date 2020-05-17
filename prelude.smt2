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
