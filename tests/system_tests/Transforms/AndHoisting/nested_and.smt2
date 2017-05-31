; RUN: %jfs-opt -and-hoist %s | %FileCheck %s

; FIXME: Should be CHECK-NEXT for y and z but there's a bug.
; Order isn't stable and we have duplicate decls.
; CHECK-DAG: (declare-fun x () Bool)
; CHECK-DAG: (declare-fun y () Bool)
; CHECK-DAG: (declare-fun z () Bool)
(declare-fun x () Bool)
(declare-fun y () Bool)
(declare-fun z () Bool)

; CHECK: (assert x)
; CHECK-NEXT: (assert (or y z))
(assert (and (or y z) x))

; CHECK-NEXT: (assert (= x x))
(assert (= x x))
(check-sat)
