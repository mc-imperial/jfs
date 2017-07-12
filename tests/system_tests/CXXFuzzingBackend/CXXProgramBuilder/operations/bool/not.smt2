; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (not (or a b)))
; CHECK: bool [[SSA0:[a-z_0-9]+]] = a || b;
; CHECK: bool [[SSA1:[a-z_0-9]+]] = !([[SSA0]]);
; CHECK-NEXT: if ([[SSA1]]) {}
(check-sat)
