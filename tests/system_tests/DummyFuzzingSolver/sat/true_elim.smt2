; RUN: %jfs -dummy %s | %FileCheck %s
(declare-fun x () (_ BitVec 32))
(assert true)
(assert true)
(assert true)
(assert true)
(check-sat)
; CHECK: {{^sat}}
