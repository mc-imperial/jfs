; RUN: %jfs-opt -dce %s | %FileCheck %s

; CHECK: (declare-fun x () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
; CHECK-NEXT: (declare-fun y () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

; CHECK: ; Start constraints (1)
; CHECK: (assert (= x y))
; CHECK-NOT: (assert (= x y))
(assert (= x y))
(assert (= x y))
(assert (= x y))
(assert (= x y))
(check-sat)
