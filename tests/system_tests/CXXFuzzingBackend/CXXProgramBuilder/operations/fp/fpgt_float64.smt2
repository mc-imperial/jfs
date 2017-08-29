; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 11 53))
(declare-fun b () (_ FloatingPoint 11 53))
; CHECK: bool [[SSA0:[a-z_0-9]+]] = a.fpgt(b)
; CHECK-NEXT: if ([[SSA0]]) {}
(assert
  (fp.gt a b)
)
(check-sat)
