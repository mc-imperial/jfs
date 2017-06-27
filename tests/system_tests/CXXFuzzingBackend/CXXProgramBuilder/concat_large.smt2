; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
(declare-fun c () (_ BitVec 8))
(declare-fun d () (_ BitVec 8))
; CHECK: BitVector<32> [[SSA0:[a-z_0-9]+]] = ((a.concat(b)).concat(c)).concat(d);
; CHECK: bool [[SSA2:[a-z_0-9]+]] = [[SSA0]] == {{[a-z_0-9]+}};
; CHECK: if ([[SSA2]]) {}
(assert (= (concat a b c d) (_ bv0 32)))
(check-sat)
