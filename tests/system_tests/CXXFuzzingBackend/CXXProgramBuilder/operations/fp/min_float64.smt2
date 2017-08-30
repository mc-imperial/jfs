; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 11 53))
(declare-fun b () (_ FloatingPoint 11 53))
; CHECK: Float<11,53> [[SSA0:[a-z_0-9]+]] = a.min(b)
; CHECK: bool [[SSA1:[a-z_0-9]+]] = [[SSA0]] == b
; CHECK-NEXT: if ([[SSA1]]) {}
(assert
  (= (fp.min a b) b)
)
(check-sat)
