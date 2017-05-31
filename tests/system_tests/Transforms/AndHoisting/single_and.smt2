; RUN: %jfs-opt -and-hoist %s | %FileCheck %s

; CHECK: (declare-fun x () (_ BitVec 32))
(declare-fun x () (_ BitVec 32))

; CHECK: (assert true)
; CHECK-NEXT: (assert true)
(assert (and true true))

; CHECK-NEXT: (assert (= x x))
(assert (= x x))
(check-sat)
