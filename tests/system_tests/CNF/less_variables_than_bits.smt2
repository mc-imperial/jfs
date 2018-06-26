; The bit-blasted form uses 15 booleans, while JFS uses 16 bits in the buffer.
; RUN: %jfs-smt2cnf %s | %FileCheck %s
(declare-fun a () (_ FloatingPoint 5 11))
(assert (not (fp.isNaN a)))
; CHECK: p cnf 17 18
; CHECK-NEXT: 1 6 0
; CHECK-NEXT: 2 6 0
; CHECK-NEXT: 3 6 0
; CHECK-NEXT: 4 6 0
; CHECK-NEXT: 5 6 0
; CHECK-NEXT: 6 -17 0
; CHECK-NEXT: -7 17 0
; CHECK-NEXT: -8 17 0
; CHECK-NEXT: -9 17 0
; CHECK-NEXT: -10 17 0
; CHECK-NEXT: -11 17 0
; CHECK-NEXT: -12 17 0
; CHECK-NEXT: -13 17 0
; CHECK-NEXT: -14 17 0
; CHECK-NEXT: -15 17 0
; CHECK-NEXT: -16 17 0
; CHECK-NEXT: -1 -2 -3 -4 -5 -6 0
; CHECK-NEXT: 7 8 9 10 11 12 13 14 15 16 -17 0
; NOTE: Z3 also prints comment lines that map constraints to CNF variables, but
; it has an off-by-one error in this output, so we omit from the test.
