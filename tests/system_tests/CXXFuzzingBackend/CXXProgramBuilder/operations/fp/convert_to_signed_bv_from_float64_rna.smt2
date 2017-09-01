; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 11 53))
; CHECK: BitVector<32> [[SSA0:[a-z_0-9]+]] = a.convertToSignedBV<32>(JFS_RM_RNA)
; CHECK: [[SSA1:[a-z_0-9+]+]] = BitVector<32>(UINT64_C(0))
; CHECK: bool [[SSA2:[a-z_0-9]+]] = [[SSA0]] == [[SSA1]]
; CHECK-NEXT: if ([[SSA2]]) {}
(assert
  (= ((_ fp.to_sbv 32) RNA a) (_ bv0 32))
)
(check-sat)
