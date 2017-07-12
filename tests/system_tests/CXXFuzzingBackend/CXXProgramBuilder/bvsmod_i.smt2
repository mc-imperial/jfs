; NOTE: This test will fail for Z3 versions that have the bug fixed by
; https://github.com/Z3Prover/z3/pull/1144
; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))
; CHECK: [[SSA0:[a-z_0-9]+]] = a.bvsmod(b);
; CHECK: bool [[SSA2:[a-z_0-9]+]] = [[SSA0]] == {{[a-z_0-9]+}};
; CHECK: if ([[SSA2]]) {}
(assert (= (bvsmod_i a b) (_ bv0 8)))
(check-sat)
