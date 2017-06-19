; RUN: %jfs-smt2cxx %s | %cxx-rt-syntax -
(declare-fun a () Bool)
(assert (or a (not a)))
(check-sat)
