; RUN: %jfs -dummy %s | %FileCheck %s
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(assert (bvugt a b))
(check-sat)
; CHECK: {{^unknown}}
