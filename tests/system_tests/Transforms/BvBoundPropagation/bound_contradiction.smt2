; RUN: %jfs-opt -bv-bound-propagation %s | %FileCheck %s
; CHECK-NOT: (declare-fun a () (_ BitVec 8))
(declare-fun a () (_ BitVec 8))

; CHECK: (assert false)
(assert (bvule #xf0 a))
(assert (bvule a #x08))
(check-sat)
