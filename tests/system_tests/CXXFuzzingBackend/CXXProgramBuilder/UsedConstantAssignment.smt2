; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun c () (_ BitVec 32))
(declare-fun d () (_ BitVec 32))
; This constant assignment should be used
; Note if constant propagation is used as a
; preprocessing step this will break.
; CHECK: BitVector<32> d = BitVector<32>(UINT64_C(13));
(assert (= d (_ bv13 32)))
(assert (bvugt c d))
(check-sat)
