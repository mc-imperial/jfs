; RUN: %jfs-opt -simplify %s | %FileCheck %s

; CHECK-NOT: (declare-fun x () (_ BitVec 8))
; CHECK: (declare-fun y () (_ BitVec 8))
; CHECK: (declare-fun z () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))
(declare-fun y () (_ BitVec 8))
(declare-fun z () (_ BitVec 8))

; CHECK: (assert (= y z))
(assert
  (=
    (ite
      (= x y)
      x
      y
    )
    z
  )
)
(check-sat)
