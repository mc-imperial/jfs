; RUN: %jfs -cxx %s | %FileCheck %s
(declare-fun buffer_0 () Bool)
(declare-fun buffer_1 () Bool)
(declare-fun buffer_2 () Bool)
(assert (or buffer_0 (or buffer_1 buffer_2)))
(check-sat)
; CHECK: {{^sat$}}
