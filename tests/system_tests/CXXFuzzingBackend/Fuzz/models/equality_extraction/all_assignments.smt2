; RUN: %jfs -get-model %s | %FileCheck %s
(declare-const a Float32)
(declare-const b Float32)
(declare-const c Float32)
(declare-const d Float32)
(declare-const e Float32)
(declare-const f Float32)
(declare-const g Float32)
(assert (= a (fp #b0 #x7f #b00000000000000000000000)))
(assert (= b (fp #b1 #x7f #b00000000000000000000000)))
(assert (= c (_ NaN 8 24)))
(assert (= d (_ +zero 8 24)))
(assert (= e (_ -zero 8 24)))
(assert (= f (_ +oo 8 24)))
(assert (= g (_ -oo 8 24)))
(check-sat)
; CHECK: {{^sat}}
; CHECK: (
; CHECK-NEXT: (define-fun a () (_ FloatingPoint 8 24) (fp #b0 #x7f #b00000000000000000000000))
; CHECK-NEXT:  (define-fun b () (_ FloatingPoint 8 24) (fp #b1 #x7f #b00000000000000000000000))
; CHECK-NEXT:  (define-fun c () (_ FloatingPoint 8 24) (_ NaN 8 24))
; CHECK-NEXT:  (define-fun d () (_ FloatingPoint 8 24) (_ +zero 8 24))
; CHECK-NEXT:  (define-fun e () (_ FloatingPoint 8 24) (_ -zero 8 24))
; CHECK-NEXT:  (define-fun f () (_ FloatingPoint 8 24) (_ +oo 8 24))
; CHECK-NEXT:  (define-fun g () (_ FloatingPoint 8 24) (_ -oo 8 24))
; CHECK-NEXT: )

