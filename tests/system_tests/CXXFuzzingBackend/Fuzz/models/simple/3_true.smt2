; RUN: %jfs %jfs_no_opt_options -get-model %s | %FileCheck %s
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

