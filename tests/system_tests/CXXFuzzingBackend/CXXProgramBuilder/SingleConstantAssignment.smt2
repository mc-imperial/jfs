; RUN: %jfs-smt2cxx %s | %cxx-rt-syntax -
(declare-fun a () (_ BitVec 32))
(assert (= a (_ bv0 32)))
(check-sat)
