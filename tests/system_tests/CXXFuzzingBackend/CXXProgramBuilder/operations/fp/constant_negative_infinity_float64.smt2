; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 11 53))
(declare-fun b () (_ FloatingPoint 11 53))
; CHECK: Float<11,53> [[SSA0:[a-z_0-9]+]] = Float<11,53>::getNegativeInfinity()
; CHECK: bool [[SSA1:[a-z_0-9]+]] = a.fpgeq([[SSA0]])
; CHECK-NEXT: if ([[SSA1]]) {}
(assert
  (fp.geq a (_ -oo 11 53))
)
(check-sat)
