; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
; CHECK: BitVector<8> [[SSA0:[a-z_0-9]+]] = (a)?(b):(c);
; CHECK: bool [[SSA1:[a-z_0-9]+]] = b == [[SSA0]];
; CHECK-NEXT: if ([[SSA1]]) {}
(assert (= b (ite a b c)))
(check-sat)
