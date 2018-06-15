; RUN: %jfs %jfs_no_opt_options -libfuzzer-seed=1 -get-model %s | %FileCheck %s
(declare-const a Float32)
(assert (= a (_ +zero 8 24)))
(check-sat)
; CHECK: {{^sat}}
; CHECK-NEXT: (define-fun a () (_ FloatingPoint 8 24)
; CHECK-NEXT: (_ +zero 8 24))
