; RUN: %jfs-opt -simplify %s | %FileCheck %s

; CHECK-NOT: (declare-fun x
(declare-fun x () (_ BitVec 8))

; simplify now removes the constraint entirely.
; CHECK: Start constraints (0)
(assert (= x x))
(check-sat)
