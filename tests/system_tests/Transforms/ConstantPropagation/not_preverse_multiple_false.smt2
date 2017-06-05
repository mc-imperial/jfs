; RUN: %jfs-opt -constant-propagation %s | %FileCheck %s

; When false gets inserted it seems
; Z3 ignores all formula that gets
; inserted into goal
(declare-fun x () (_ BitVec 8))

; This gets removed too
(assert (bvugt x #x01))

; CHECK: (assert false)
(assert false)
(assert false)
(assert false)
(assert false)
(assert false)

