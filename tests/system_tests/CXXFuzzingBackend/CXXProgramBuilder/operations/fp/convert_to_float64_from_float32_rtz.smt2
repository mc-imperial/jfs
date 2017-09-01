; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 8 24))
; CHECK: Float<11,53> [[SSA0:[a-z_0-9]+]] = a.convertToFloat<11,53>(JFS_RM_RTZ)
; CHECK: bool [[SSA1:[a-z_0-9]+]] = [[SSA0]].isNaN()
; CHECK-NEXT: if ([[SSA1]]) {}
(assert
  (fp.isNaN ((_ to_fp 11 53) RTZ a))
)
(check-sat)
