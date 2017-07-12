; FIXME: BvBoundPropagationPass is broken
; XFAIL: *
; RUN: %jfs -dummy %s | %FileCheck %s
; CHECK-NOT: (declare-fun a () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))

(assert (bvule #xf0 a))
(assert (bvule a #x08))
(check-sat)
; CHECK: {{^unsat}}
