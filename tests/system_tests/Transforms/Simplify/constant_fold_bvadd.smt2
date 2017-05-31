; RUN: %jfs-opt -simplify %s | %FileCheck %s

; CHECK: (declare-fun x () (_ BitVec 8))
(declare-fun x () (_ BitVec 8))

; CHECK: (assert (= x #xf1))
(assert (= x (bvadd #x01 #xf0)))
(check-sat)
