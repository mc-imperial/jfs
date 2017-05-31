; RUN: %jfs-opt -simplify %s | %FileCheck %s

; CHECK-NOT: (declare-fun x
(declare-fun x () (_ BitVec 8))

; CHECK: (assert false)
(assert (not (= x x)))
(check-sat)
