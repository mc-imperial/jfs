; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ BitVec 8))
; CHECK: BitVector<8> [[SSA0:[a-z_0-9]+]] = a.bvneg();
; CHECK: bool [[SSA2:[a-z_0-9]+]] = [[SSA0]] == {{[a-z_0-9]+}};
; CHECK: if ([[SSA2]]) {}
(assert (= (bvneg a) (_ bv255 8)))
(check-sat)
