; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
; CHECK: bool [[SSA0:[a-z_0-9]+]] = a == b;
; CHECK: bool [[SSA1:[a-z_0-9]+]] = a == c;
; CHECK: bool [[SSA2:[a-z_0-9]+]] = [[SSA0]] || [[SSA1]];
; CHECK-NEXT: if ([[SSA2]]) {}
; Note: We have to use or here to avoid equalities being
; removed.
(assert (or (= a b) (= a c)))
(check-sat)
