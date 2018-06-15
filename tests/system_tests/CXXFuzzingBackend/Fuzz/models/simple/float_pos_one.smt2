; RUN: %jfs %jfs_no_opt_options -libfuzzer-seed=1 -get-model %s | %FileCheck %s
(declare-const a Float32)
(assert (= a (fp #b0 #x7f #b00000000000000000000000)))
(check-sat)
; CHECK: {{^sat}}
; CHECK-NEXT: (define-fun a () (_ FloatingPoint 8 24)
; CHECK-NEXT: (fp #b0 #x7f #b00000000000000000000000))
