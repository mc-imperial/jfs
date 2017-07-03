; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun c () (_ BitVec 32))
; This is probably the best we can do.
; CHECK: bool [[SSA0:[a-z_0-9]+]] = false;
; CHECK-NEXT: if ([[SSA0]]) {}
(assert (= c (_ bv13 32)))
(assert (= c (_ bv0 32)))
(check-sat)
