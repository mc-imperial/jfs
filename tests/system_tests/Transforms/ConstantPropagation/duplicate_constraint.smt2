; RUN: %jfs-opt -constant-propagation %s | %FileCheck %s
; CHECK: (declare-fun x () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

; Z3 tactic seems to remove duplicate constraints
; CHECK: (assert (= x #xfe))
; CHECK-NOT: (assert (= x #xfe))
(assert (= x #xfe))
(assert (= x #xfe))
(assert (= x #xfe))
(assert (= x #xfe))
(assert (= x #xfe))
(check-sat)
