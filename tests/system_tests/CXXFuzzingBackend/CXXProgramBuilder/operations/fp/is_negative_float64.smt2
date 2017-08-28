; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 11 53))
; CHECK: bool [[SSA0:[a-z_0-9]+]] = a.isNegative()
; CHECK-NEXT: if ([[SSA0]]) {}
(assert
  (fp.isNegative a)
)
(check-sat)
