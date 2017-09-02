; This benchmark causes problems because Z3's simplifier fails to
; constant fold the values. This required special handling of this
; case when invoking LibFuzzer.
; See https://github.com/Z3Prover/z3/issues/1242

; RUN: %jfs -cxx %s | %FileCheck %s

(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :source |Christoph M. Wintersteiger (cwinter@microsoft.com). Randomly generated floating-point testcases.|)
; Rounding mode: to zero
; Precision: double (11/53)
; X = 1.24692151349674151816770972800441086292266845703125p-850 {+ 1112035636173684 -850 (1.6609e-256)}
; Y = -1.7185126679306905739252897546975873410701751708984375p-150 {- 3235893383553639 -150 (-1.20407e-045)}
; 1.24692151349674151816770972800441086292266845703125p-850 m -1.7185126679306905739252897546975873410701751708984375p-150 == -1.7185126679306905739252897546975873410701751708984375p-150
; [HW: -1.7185126679306905739252897546975873410701751708984375p-150] 

; mpf : - 3235893383553639 -150
; mpfd: - 3235893383553639 -150 (-1.20407e-045) class: Neg. norm. non-zero
; hwf : - 3235893383553639 -150 (-1.20407e-045) class: Neg. norm. non-zero

(set-logic QF_FP)
(set-info :status sat)
(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () FPN)
(declare-fun y () FPN)
(declare-fun r () FPN)
(assert (= x (fp #b0 #b00010101101 #b0011111100110110001111111001000100100101101101110100)))
(assert (= y (fp #b1 #b01101101001 #b1011011111110000011100100011101010000110001001100111)))
(assert (= r (fp #b1 #b01101101001 #b1011011111110000011100100011101010000110001001100111)))
(assert (= (fp.min x y) r))
; CHECK: {{^sat$}}
(check-sat)
(exit)
