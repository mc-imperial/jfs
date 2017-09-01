; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 11 53))
; CHECK: Float<8,24> [[SSA0:[a-z_0-9]+]] = a.convertToFloat<8,24>(JFS_RM_RTN)
; CHECK: bool [[SSA1:[a-z_0-9]+]] = [[SSA0]].isNaN()
; CHECK-NEXT: if ([[SSA1]]) {}
(assert
  (fp.isNaN ((_ to_fp 8 24) RTN a))
)
(check-sat)
