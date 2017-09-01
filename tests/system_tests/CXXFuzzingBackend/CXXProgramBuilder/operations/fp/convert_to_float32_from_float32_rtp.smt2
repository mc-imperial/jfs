; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 8 24))
; CHECK: Float<8,24> [[SSA0:[a-z_0-9]+]] = a.convertToFloat<8,24>(JFS_RM_RTP)
; CHECK: bool [[SSA1:[a-z_0-9]+]] = [[SSA0]].isNaN()
; CHECK-NEXT: if ([[SSA1]]) {}
(assert
  (fp.isNaN ((_ to_fp 8 24) RTP a))
)
(check-sat)
