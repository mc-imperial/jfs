; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
; CHECK: bool [[SSA0:[a-z_0-9]+]] = a ^ b;
; CHECK-NEXT: if ([[SSA0]]) {}
(assert (xor a b))
(check-sat)
