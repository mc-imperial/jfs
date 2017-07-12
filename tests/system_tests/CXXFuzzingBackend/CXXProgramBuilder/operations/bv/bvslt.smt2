; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
; CHECK: [[SSA0:[a-z_0-9]+]] = a.bvslt(b);
; CHECK-NEXT: if ([[SSA0]]) {}
(assert (bvslt a b))
(check-sat)
