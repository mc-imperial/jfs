; RUN: %jfs -get-model %s | %FileCheck %s
; FIXME: jfs doesn't actually use this option.
(set-option :produce-models true)
(check-sat)
; FIXME: The parser fails on (get-model) so comment out for now.
;(get-model)
; CHECK: {{^sat}}
; Empty model
; CHECK-NEXT: ()
