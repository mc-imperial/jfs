; RUN: %jfs-opt -simplify %s | %FileCheck %s

; CHECK-NOT: (declare-fun x
(declare-fun x () (_ BitVec 8))

; CHECK: (assert true)
(assert (= x x))
(check-sat)
