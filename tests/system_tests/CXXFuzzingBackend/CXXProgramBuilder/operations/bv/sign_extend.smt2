; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ BitVec 8))
; CHECK: BitVector<12> [[SSA0:[a-z_0-9]+]] = a.signExtend<4>();
; CHECK: bool [[SSA2:[a-z_0-9]+]] = [[SSA0]] == {{[a-z_0-9]+}};
; CHECK: if ([[SSA2]]) {}
(assert (= ((_ sign_extend 4) a) (_ bv0 12)))
(check-sat)
