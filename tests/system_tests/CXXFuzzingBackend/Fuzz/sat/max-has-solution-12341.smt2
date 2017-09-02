; This benchmark causes problems because Z3's simplifier fails to
; constant fold the values. This required special handling of this
; case when invoking LibFuzzer.
; See https://github.com/Z3Prover/z3/issues/1242

; RUN: %jfs -cxx %s | %FileCheck %s

(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :source |Christoph M. Wintersteiger (cwinter@microsoft.com). Randomly generated floating-point testcases.|)
; Rounding mode: to negative
; Precision: double (11/53)
; X = 1.6908442241812353667995694195269607007503509521484375p-775 {+ 3111285790593671 -775 (8.50858e-234)}
; Y = -1.25849312345896446885262776049785315990447998046875p-663 {- 1164149534487628 -663 (-3.28824e-200)}
; 1.6908442241812353667995694195269607007503509521484375p-775 M -1.25849312345896446885262776049785315990447998046875p-663 == 1.6908442241812353667995694195269607007503509521484375p-775
; [HW: 1.6908442241812353667995694195269607007503509521484375p-775] 

; mpf : + 3111285790593671 -775
; mpfd: + 3111285790593671 -775 (8.50858e-234) class: Pos. norm. non-zero
; hwf : + 3111285790593671 -775 (8.50858e-234) class: Pos. norm. non-zero

(set-logic QF_FP)
(set-info :status sat)
(define-sort FPN () (_ FloatingPoint 11 53))
(declare-fun x () FPN)
(declare-fun y () FPN)
(declare-fun r () FPN)
(assert (= x (fp #b0 #b00011111000 #b1011000011011011001010101100010101111101001010000111)))
(assert (= y (fp #b1 #b00101101000 #b0100001000101100100110101111011101111111010001001100)))
(assert (= r (fp #b0 #b00011111000 #b1011000011011011001010101100010101111101001010000111)))
(assert (= (fp.max x y) r))
(check-sat)
; CHECK: {{^sat$}}
(exit)
