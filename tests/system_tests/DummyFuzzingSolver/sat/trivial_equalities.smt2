; RUN: %jfs -dummy %s | %FileCheck %s
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
(assert (= a b))
(assert (= b c))
(check-sat)
; CHECK: {{^sat}}
