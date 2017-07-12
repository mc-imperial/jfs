; FIXME: BvBoundPropagationPass is broken
; XFAIL: *
; RUN: %jfs -dummy %s | %FileCheck %s
; CHECK-NOT: (declare-fun a () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))

(assert (bvugt a #xfe))
(assert (bvult a #xff))
(check-sat)
; CHECK: {{^unsat}}
