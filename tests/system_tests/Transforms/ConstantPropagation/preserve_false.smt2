; RUN: %jfs-opt -constant-propagation %s | %FileCheck %s
; CHECK: (assert false)
(assert false)
