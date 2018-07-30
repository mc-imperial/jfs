; RUN: rm -rf %t-output-dir
; RUN: %jfs %jfs_no_opt_options -get-model -debug-save-model -keep-output-dir -output-dir=%t-output-dir %s | %FileCheck %s
(declare-const a Float32)
(assert (= a (_ NaN 8 24)))
(check-sat)
; CHECK: {{^sat}}
; CHECK-NEXT: (
; CHECK-NEXT: (define-fun a () (_ FloatingPoint 8 24) (_ NaN 8 24))
; CHECK-NEXT: )

; RUN: base64 -i %t-output-dir/model-output | %FileCheck -check-prefix=CHECK-MODEL %s
; CHECK-MODEL: AADAfw==
; NOTE: This differs from the loaded fuzzer artifact (0xFFFFFFFF), which is one
; of many possible NaN representations.  When saving, we use a canonical NaN
; representation (0x7FC00000).
