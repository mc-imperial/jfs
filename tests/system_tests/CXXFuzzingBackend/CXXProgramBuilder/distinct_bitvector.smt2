; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
; CHECK: bool [[SSA0:[a-z_0-9]+]] = ( a != b ) && ( a != c ) && ( a != d ) && ( b != c ) && ( b != d ) && ( c != d );
; CHECK-NEXT: if ([[SSA0]]) {}
(assert (distinct a b c d))
(check-sat)
