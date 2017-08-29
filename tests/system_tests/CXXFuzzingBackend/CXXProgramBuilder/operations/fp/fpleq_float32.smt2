; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
; CHECK: bool [[SSA0:[a-z_0-9]+]] = a.fpleq(b)
; CHECK-NEXT: if ([[SSA0]]) {}
(assert
  (fp.leq a b)
)
(check-sat)
