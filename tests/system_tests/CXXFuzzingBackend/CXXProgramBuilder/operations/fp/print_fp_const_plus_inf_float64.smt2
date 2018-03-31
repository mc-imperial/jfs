; RUN: %jfs-smt2cxx %s > %t.cxx
; RUN: %cxx-rt-syntax %t.cxx
; RUN: %FileCheck -input-file=%t.cxx %s

; This example is constructed such that the CXXProgramBuilder
; has to emit the `d` constant. This requires that constant
; propagation has not run.

(declare-fun c () (_ FloatingPoint 11 53))
(declare-fun d () (_ FloatingPoint 11 53))
; CHECK: Float<11,53> d = Float<11,53>::getPositiveInfinity()
(assert (= d (_ +oo 11 53)))
(assert (not (fp.isNaN (fp.add RNE c d))))
(check-sat)
