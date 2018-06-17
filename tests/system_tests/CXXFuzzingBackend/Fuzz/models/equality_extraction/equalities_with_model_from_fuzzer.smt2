; RUN: %jfs -cxx -get-model -validate-model %s | %FileCheck %s
; FIXME: Make LibPureRandomFuzzer work on this example?
; REQUIRES: LibFuzzer
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
; Equality extraction should determine on model conversion that
; the no assignment is provided and that it should provide its own
; in order to enforce the equalities.
(assert (= a b))
(assert (= b c))
; These two constraints imply that value of c must be (_ bv1 32)
(assert (bvult c (_ bv2 32)))
(assert (bvugt c (_ bv0 32)))
(check-sat)
; CHECK: {{^sat}}
; CHECK-NEXT: (
; CHECK-NEXT: (define-fun a () (_ BitVec 32) #x00000001)
; CHECK-NEXT: (define-fun b () (_ BitVec 32) #x00000001)
; CHECK-NEXT: (define-fun c () (_ BitVec 32) #x00000001)
; CHECK-NEXT: )

