; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
; CHECK: bool [[SSA0:[a-z_0-9]+]] = a && b;
; CHECK-NEXT: if ([[SSA0]]) {}
; CHECK: bool [[SSA1:[a-z_0-9]+]] = b && c;
; CHECK-NEXT: if ([[SSA1]]) {}
(assert (and (and a b) (and b c)))
(check-sat)
