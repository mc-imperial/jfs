; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ BitVec 8))
; CHECK: BitVector<2> [[SSA0:[a-z_0-9]+]] = a.extract<2>(7,6);
; CHECK: bool [[SSA2:[a-z_0-9]+]] = [[SSA0]] == {{[a-z_0-9]+}};
; CHECK: if ([[SSA2]]) {}
(assert (= ((_ extract 7 6) a) (_ bv0 2)))
(check-sat)
