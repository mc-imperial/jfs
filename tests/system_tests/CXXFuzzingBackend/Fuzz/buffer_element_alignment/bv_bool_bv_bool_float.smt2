; RUN: %jfs -byte-aligned-buffer-elements=false %s | %FileCheck %s
; RUN: %jfs -byte-aligned-buffer-elements %s | %FileCheck %s

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () (_ BitVec 2))
(declare-fun e () (_ BitVec 19))
(declare-fun f () Float32)
(assert (or a b))
(assert (bvult d #b11))
(assert (bvult e #b1010101010101001011))
(assert (fp.eq f f))
(assert (or b c))
(check-sat)
; CHECK: {{^sat}}
