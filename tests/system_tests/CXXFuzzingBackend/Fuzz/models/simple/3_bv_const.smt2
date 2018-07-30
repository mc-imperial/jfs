; RUN: rm -rf %t-output-dir
; RUN: %jfs %jfs_no_opt_options -get-model -debug-save-model -keep-output-dir -output-dir=%t-output-dir %s | %FileCheck %s
(declare-const a (_ BitVec 8))
(declare-const b (_ BitVec 8))
(declare-const c (_ BitVec 8))
(assert (= a #xff))
(assert (= b #x0a))
(assert (= c #x00))
(check-sat)
; CHECK: {{^sat}}
; CHECK: (
; CHECK-NEXT: (define-fun a () (_ BitVec 8) #xff)
; CHECK-NEXT: (define-fun b () (_ BitVec 8) #x0a)
; CHECK-NEXT: (define-fun c () (_ BitVec 8) #x00)
; CHECK-NEXT: )

; RUN: base64 -i %t-output-dir/model-output | %FileCheck -check-prefix=CHECK-MODEL %s
; CHECK-MODEL: /woA
