; RUN: %jfs-opt -constant-propagation %s | %FileCheck %s
; CHECK: (declare-fun x () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
; CHECK-NEXT: (declare-fun y () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
; CHECK-NEXT: (declare-fun z () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))

; NOTE: Current implementation of constant propagation hoists ands and seems
; to do some simplication of its own. I don't actually want this as I want good
; separation of concerns.

; CHECK-DAG: (assert (= z #xfe))
(assert (and (= x z) (= z x) ))

; CHECK-DAG: (assert (= x #xfe))
(assert (= x #xfe))

(assert (bvugt y x))
; CHECK-NEXT: (assert (not (bvule y #xfe)))

(check-sat)
