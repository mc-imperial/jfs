; RUN: %jfs -cxx -get-model %s | %FileCheck %s
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
; Equality extraction should determine on model conversion that
; the no assignment is provided and that it should provide its own
; in order to enforce the equalities.
(assert (= a b))
(assert (= b c))
(check-sat)
; CHECK: {{^sat}}
; CHECK-NEXT: (
; CHECK-NEXT: (define-fun a () (_ BitVec 32) #x00000000)
; CHECK-NEXT: (define-fun b () (_ BitVec 32) #x00000000)
; CHECK-NEXT: (define-fun c () (_ BitVec 32) #x00000000)
; CHECK-NEXT: )

