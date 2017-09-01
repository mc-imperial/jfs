; RUN: %jfs -cxx -max-time=3 %s | %FileCheck %s
(declare-fun a () (_ FloatingPoint 8 24))
(declare-fun b () (_ FloatingPoint 8 24))
(assert (fp.eq a (fp #b0 #x86 #b00000000000000000000000)))
(assert (fp.eq b (fp #b0 #x86 #b00000000000000000000001)))
(check-sat)
; CHECK: {{^sat$}}
(exit)
