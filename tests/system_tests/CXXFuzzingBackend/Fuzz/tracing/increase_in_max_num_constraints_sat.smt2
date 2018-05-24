; RUN: rm -rf %t-output-dir
; RUN: %jfs -disable-standard-passes -redirect-libfuzzer-output=1 -output-dir=%t-output-dir -keep-output-dir -trace-max-num-satisfied-constraints -cxx %s | %FileCheck -check-prefix=CHECK-SAT %s

; RUN: %FileCheck -check-prefix=CHECK-LIBFUZZER -input-file=%t-output-dir/libfuzzer.stderr.txt %s
(declare-fun buffer_0 () Bool)
(declare-fun buffer_1 () Bool)
(declare-fun buffer_2 () Bool)
(declare-fun buffer_3 () Bool)
(assert (or buffer_0 buffer_1))
(assert (or buffer_1 buffer_2))
(assert (or buffer_2 buffer_3))
(check-sat)

; CHECK-SAT: {{^sat$}}

; CHECK-LIBFUZZER: JFS INFO: Max num constraints satisfied increased from 0 to 1 (out of 3)
; CHECK-LIBFUZZER: JFS INFO: Max num constraints satisfied increased from 1 to 2 (out of 3)
; CHECK-LIBFUZZER: JFS INFO: Max num constraints satisfied increased from 2 to 3 (out of 3)

