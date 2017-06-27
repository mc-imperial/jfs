; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () Bool)
; CHECK: bool [[SSA0:[a-z_0-9]+]] = ( a != b );
; CHECK-NEXT: if ([[SSA0]]) {}
(assert (distinct a b))
(check-sat)
