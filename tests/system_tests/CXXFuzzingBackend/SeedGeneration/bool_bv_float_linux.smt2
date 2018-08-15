; FIXME: This test doesn't have stable output between Darwin and Linux.
; This is likely a difference in behaviour of the random number generator
; between libstdc++ and libcxx.
; REQUIRES: linux
; RUN: %jfs -v=2 \
; RUN: -sm-all-ones-seed=0 \
; RUN: -sm-all-zeros-seed=0 \
; RUN: -sm-special-constant-seeds=true \
; RUN: -sm-max-num-seed=8 %s 2>&1 | %FileCheck %s

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () (_ BitVec 2))
(declare-fun e () (_ BitVec 19))
(declare-fun f () Float32)
(declare-fun g () Float64)
(assert (or a b))
(assert (bvult d #b11))
(assert (bvult e #b1010101010101001011))
(assert (fp.eq f f))
(assert (fp.eq g g))
(assert (or b c))
(check-sat)

; CHECK: (Sort: Bool, Assignment: false)
; CHECK-NEXT: (Sort: Bool, Assignment: false)
; CHECK-NEXT: (Sort: (_ BitVec 2), Assignment: #b11)
; CHECK-NEXT: (Sort: (_ BitVec 19), Assignment: #b0000000000000000000)
; CHECK-NEXT: (Sort: (_ FloatingPoint 8 24), Assignment: (fp #b0 #x7f #b00000000000000000000000))
; CHECK-NEXT: (Sort: (_ FloatingPoint 11 53), Assignment: (fp #b1 #b11111111110 #xfffffffffffff))
; CHECK-NEXT: (Sort: Bool, Assignment: false)

; CHECK: (Sort: Bool, Assignment: false)
; CHECK-NEXT: (Sort: Bool, Assignment: true)
; CHECK-NEXT: (Sort: (_ BitVec 2), Assignment: #b01)
; CHECK-NEXT: (Sort: (_ BitVec 19), Assignment: #b0000000000000000000)
; CHECK-NEXT: (Sort: (_ FloatingPoint 8 24), Assignment: (fp #b0 #x00 #b11111111111111111111111))
; CHECK-NEXT: (Sort: (_ FloatingPoint 11 53), Assignment: (fp #b1 #b00000000000 #xfffffffffffff))
; CHECK-NEXT: (Sort: Bool, Assignment: false)

; CHECK: (Sort: Bool, Assignment: false)
; CHECK-NEXT: (Sort: Bool, Assignment: false)
; CHECK-NEXT: (Sort: (_ BitVec 2), Assignment: #b01)
; CHECK-NEXT: (Sort: (_ BitVec 19), Assignment: #b1010101010101001011)
; CHECK-NEXT: (Sort: (_ FloatingPoint 8 24), Assignment: (fp #b0 #x00 #b00000000000000000000001))
; CHECK-NEXT: (Sort: (_ FloatingPoint 11 53), Assignment: (_ NaN 11 53))
; CHECK-NEXT: (Sort: Bool, Assignment: false)

; CHECK: (Sort: Bool, Assignment: true)
; CHECK-NEXT: (Sort: Bool, Assignment: false)
; CHECK-NEXT: (Sort: (_ BitVec 2), Assignment: #b01)
; CHECK-NEXT: (Sort: (_ BitVec 19), Assignment: #b0000000000000000001)
; CHECK-NEXT: (Sort: (_ FloatingPoint 8 24), Assignment: (_ -zero 8 24))
; CHECK-NEXT: (Sort: (_ FloatingPoint 11 53), Assignment: (_ -zero 11 53))
; CHECK-NEXT: (Sort: Bool, Assignment: false)

; CHECK: (Sort: Bool, Assignment: true)
; CHECK-NEXT: (Sort: Bool, Assignment: true)
; CHECK-NEXT: (Sort: (_ BitVec 2), Assignment: #b01)
; CHECK-NEXT: (Sort: (_ BitVec 19), Assignment: #b0000000000000000001)
; CHECK-NEXT: (Sort: (_ FloatingPoint 8 24), Assignment: (fp #b0 #x00 #b00000000000000000000001))
; CHECK-NEXT: (Sort: (_ FloatingPoint 11 53), Assignment: (fp #b0 #b01111111111 #x0000000000000))
; CHECK-NEXT: (Sort: Bool, Assignment: false)

; CHECK: (Sort: Bool, Assignment: true)
; CHECK-NEXT: (Sort: Bool, Assignment: true)
; CHECK-NEXT: (Sort: (_ BitVec 2), Assignment: #b01)
; CHECK-NEXT: (Sort: (_ BitVec 19), Assignment: #b0000000000000000000)
; CHECK-NEXT: (Sort: (_ FloatingPoint 8 24), Assignment: (_ NaN 8 24))
; CHECK-NEXT: (Sort: (_ FloatingPoint 11 53), Assignment: (fp #b1 #b11111111110 #xfffffffffffff))
; CHECK-NEXT: (Sort: Bool, Assignment: false)

; CHECK: (Sort: Bool, Assignment: true)
; CHECK-NEXT: (Sort: Bool, Assignment: false)
; CHECK-NEXT: (Sort: (_ BitVec 2), Assignment: #b11)
; CHECK-NEXT: (Sort: (_ BitVec 19), Assignment: #b1010101010101001011)
; CHECK-NEXT: (Sort: (_ FloatingPoint 8 24), Assignment: (fp #b0 #x01 #b00000000000000000000000))
; CHECK-NEXT: (Sort: (_ FloatingPoint 11 53), Assignment: (fp #b1 #b11111111110 #xfffffffffffff))
; CHECK-NEXT: (Sort: Bool, Assignment: true)

; CHECK: (Sort: Bool, Assignment: false)
; CHECK-NEXT: (Sort: Bool, Assignment: true)
; CHECK-NEXT: (Sort: (_ BitVec 2), Assignment: #b11)
; CHECK-NEXT: (Sort: (_ BitVec 19), Assignment: #b1111111111111111111)
; CHECK-NEXT: (Sort: (_ FloatingPoint 8 24), Assignment: (fp #b0 #xfe #b11111111111111111111111))
; CHECK-NEXT: (Sort: (_ FloatingPoint 11 53), Assignment: (_ +zero 11 53))
; CHECK-NEXT: (Sort: Bool, Assignment: false)

; CHECK: (SeedManager wrote 8 seeds (15 bytes each))
