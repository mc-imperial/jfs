; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
; CHECK: Float<8,24> [[SSA0:[a-z_0-9]+]] = Float<8,24>::getNegativeInfinity()
; CHECK: bool [[SSA1:[a-z_0-9]+]] = a.fpgeq([[SSA0]])
; CHECK-NEXT: if ([[SSA1]]) {}
(assert
  (fp.geq a (_ -oo 8 24))
)
(check-sat)
