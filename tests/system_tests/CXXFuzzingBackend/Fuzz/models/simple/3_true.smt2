; RUN: rm -rf %t-output-dir
; RUN: %jfs %jfs_no_opt_options -get-model -debug-save-model -keep-output-dir -output-dir=%t-output-dir %s | %FileCheck %s
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (and a b c))
(check-sat)
; CHECK: {{^sat}}
; CHECK-NEXT: (
; CHECK-NEXT: (define-fun a () Bool true)
; CHECK-NEXT: (define-fun b () Bool true)
; CHECK-NEXT: (define-fun c () Bool true)
; CHECK-NEXT: )

; RUN: base64 -i %t-output-dir/model-output | %FileCheck -check-prefix=CHECK-MODEL %s
; CHECK-MODEL: Bw==
; NOTE: This differs from the loaded fuzzer artifact (0xFF) because it only
; saves the bits needed to represent the 3 bools (0x07).
