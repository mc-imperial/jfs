; RUN: %jfs-opt -tce %s | %FileCheck %s
; CHECK: (declare-fun x () (_ BitVec 32))
; CHECK-NEXT: (declare-fun y () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

; CHECK: ; Start constraints (1)
; CHECK: (assert (not (= x y)))
(assert (not (= x y)))

; CHECK-NOT: (assert true)
(assert true)
(assert true)
(assert true)
(assert true)
(check-sat)
