; RUN: %jfs -v=1 -cxx %s > %t.stdout 2> %t.stderr
; RUN: %FileCheck -check-prefix=CHECK-STDOUT -input-file=%t.stdout %s
; RUN: %FileCheck -check-prefix=CHECK-STDERR -input-file=%t.stderr %s

; This size is not supported natively so we should report unknown
(declare-fun a () (_ BitVec 128))
(declare-fun b () (_ BitVec 128))
(declare-fun c () (_ BitVec 128))
(assert (= c (bvadd a b)))
(check-sat)

; CHECK-STDOUT: {{^unknown$}}
; CHECK-STDERR: BitVector width 128 not supported
