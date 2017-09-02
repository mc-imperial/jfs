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
(assert (= x (fp #b0 #b00011111000 #b1011000011011011001010101100010101111101001010000111)))
(assert (= y (fp #b1 #b00101101000 #b0100001000101100100110101111011101111111010001001100)))
(assert (= r (fp #b1 #b00011111000 #b1011000011011011001010101100010101111101001010000111)))
(assert (= (fp.max x y) r))
; CHECK: {{^unsat$}}
(check-sat)
(exit)
