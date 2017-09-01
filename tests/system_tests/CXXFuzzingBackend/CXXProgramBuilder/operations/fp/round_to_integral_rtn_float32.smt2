; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
; CHECK: Float<8,24> [[SSA0:[a-z_0-9]+]] = a.roundToIntegral(JFS_RM_RTN)
; CHECK: bool [[SSA1:[a-z_0-9]+]] = [[SSA0]].ieeeEquals(b)
; CHECK-NEXT: if ([[SSA1]]) {}
(assert
  (fp.eq (fp.roundToIntegral RTN a) b)
)
(check-sat)
