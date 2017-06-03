; RUN: %jfs-opt -constant-propagation %s | %FileCheck %s
; CHECK: (declare-fun x () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
; CHECK-NEXT: (declare-fun y () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))

; CHECK: (assert (= x #xfe))
(assert (= x #xfe))

(assert (bvugt y x))
; CHECK-NEXT: (assert (not (bvule y #xfe)))

(check-sat)
