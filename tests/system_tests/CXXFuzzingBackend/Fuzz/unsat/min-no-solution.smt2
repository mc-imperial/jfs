; This benchmark causes problems because Z3's simplifier fails to
; constant fold the values. This required special handling of this
; case when invoking LibFuzzer.
; See https://github.com/Z3Prover/z3/issues/1242

; RUN: %jfs -cxx %s | %FileCheck %s

(set-info :smt-lib-version 2.6)
(set-logic QF_FP)
(set-info :status sat)
(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () FPN)
(declare-fun y () FPN)
(declare-fun r () FPN)
(assert (= x (fp #b0 #b00010101101 #b0011111100110110001111111001000100100101101101110100)))
(assert (= y (fp #b1 #b01101101001 #b1011011111110000011100100011101010000110001001100111)))
(assert (= r (fp #b1 #b11101101001 #b1011011111110000011100100011101010000110001001100111)))
(assert (= (fp.min x y) r))

; CHECK: {{^unsat$}}
(check-sat)
(exit)
