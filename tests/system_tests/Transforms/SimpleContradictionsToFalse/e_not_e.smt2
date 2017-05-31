; RUN: %jfs-opt -sctf %s | %FileCheck %s

; CHECK: (declare-fun x () (_ BitVec 32))
; CHECK-NEXT: (declare-fun y () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))

; CHECK: ; Start constraints (3)
; CHECK-NEXT: (assert (= (bvxor x y) x))
(assert (= (bvxor x y) x))
; CHECK-NEXT: (assert false)
(assert (not (= x y)))
; CHECK-NEXT: (assert false)
(assert (= x y))
(check-sat)
