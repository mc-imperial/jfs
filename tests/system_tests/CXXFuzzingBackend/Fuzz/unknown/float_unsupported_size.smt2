; RUN: %jfs -cxx %s | %FileCheck %s

; This size is not supported natively so we should report unknown
(declare-fun a () (_ FloatingPoint 5 11))
(assert (not (fp.isNaN a)))
(check-sat)
; CHECK: {{^unknown$}}
