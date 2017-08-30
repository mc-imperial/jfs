; RUN: %jfs -cxx %s | %FileCheck %s
(declare-fun a () (_ FloatingPoint 11 53))
; FIXME: We need to figure out a way to write the test better.
; It seems that Z3's simplifier will fold Z3_OP_FPA_TO_FP operations
; into Z3_OP_FPA_NUM when all three args are constant. For some reason
; Z3's parser doesn't fold this at parse time.
(assert (fp.lt (fp #b0 #b10000000000 #x0000000000000) a))
; CHECK: {{^sat$}}
(check-sat)
