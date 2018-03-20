; RUN: %jfs -v=1 -cxx %s > %t.stdout 2> %t.stderr
; RUN: %FileCheck -check-prefix=CHECK-STDOUT -input-file=%t.stdout %s
; RUN: %FileCheck -check-prefix=CHECK-STDERR -input-file=%t.stderr %s

; This size is not supported natively so we should report unknown
(declare-fun a () (_ FloatingPoint 5 11))
(assert (not (fp.isNaN a)))
(check-sat)

; CHECK-STDOUT: {{^unknown$}}
; CHECK-STDERR: FloatingPoint sort "(_ FloatingPoint 5 11)" not supported
