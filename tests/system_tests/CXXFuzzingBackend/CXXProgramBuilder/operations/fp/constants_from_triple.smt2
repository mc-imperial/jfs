; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; FIXME: Add FileCheck test. Not doing now because
; design is in flux
(declare-fun a () (_ FloatingPoint 8 24))
(assert
  (or
    (= a (fp #b0 #b00000000 #b00000000000000000000000))
    (= a (fp #b1 #b00000000 #b00000000000000000000000))
  )
)
(check-sat)
