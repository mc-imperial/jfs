; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(set-logic QF_FP)
(set-info :status sat)
(define-sort FPN () (_ FloatingPoint 8 24))
(declare-fun x () FPN)
(declare-fun y () FPN)

; HACK: This name is a special internal Z3 function. We can't directly write
; it because Z3's parser won't accept it so we declare it here.
(declare-fun fp.min_unspecified ((FPN) (FPN)) FPN)

; CHECK: Float<8,24> [[SSA0:[a-z_0-9]+]] = x.min(y)
; CHECK: bool [[SSA1:[a-z_0-9]+]] = [[SSA0]] == x
; CHECK-NEXT: if ([[SSA1]]) {}
(assert (= (fp.min_unspecified x y) x))
(check-sat)
(exit)
