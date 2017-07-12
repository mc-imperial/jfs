; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ BitVec 8))
; CHECK: const BitVector<8> [[SSA0:[a-z_0-9]+]] = BitVector<8>(UINT64_C(0));
; CHECK: const BitVector<8> [[SSA1:[a-z_0-9]+]] = a.bvsdiv([[SSA0]]);
; CHECK: const bool [[SSA2:[a-z_0-9]+]] = [[SSA1]] == [[SSA0]];
; CHECK: if ([[SSA2]]) {}
(assert (= (bvsdiv a (_ bv0 8)) (_ bv0 8)))
(check-sat)
