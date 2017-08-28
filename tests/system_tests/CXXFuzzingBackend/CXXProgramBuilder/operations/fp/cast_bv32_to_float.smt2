; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; FIXME: Add FileCheck test. Not doing now because
; design is in flux
(declare-fun a () (_ BitVec 32))
(assert
  (or
    (=
      ((_ to_fp 8 24) a)
      (fp #b0 #b00000000 #b00000000000000000000000)
    )
    (=
      ((_ to_fp 8 24) a)
      (fp #b1 #b00000000 #b00000000000000000000000)
    )
  )
)
(check-sat)
