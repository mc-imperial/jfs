; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(declare-fun c () (_ FloatingPoint 8 24))
; CHECK: Float<8,24> a = Float<8,24>(BitVector<1>(UINT64_C(0)), BitVector<8>(UINT64_C(134)), BitVector<23>(UINT64_C(0)))
(assert (= a (fp #b0 #x86 #b00000000000000000000000)))
(assert (= b (fp #b0 #x86 #b00000000000000000000001)))
(assert (not (fp.isNaN a)))
(assert (not (fp.isNaN (fp.add RNE a c))))
(check-sat)
