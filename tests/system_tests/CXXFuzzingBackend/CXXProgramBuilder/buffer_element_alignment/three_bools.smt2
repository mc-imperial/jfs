; RUN: %jfs-smt2cxx -byte-aligned-buffer-elements=false %s > %t-no-align.cpp
; RUN: %cxx-rt-syntax %t-no-align.cpp
; RUN: %FileCheck -check-prefixes CHECK-COMMON,CHECK-NO-ALIGN -input-file=%t-no-align.cpp %s
; RUN: %jfs-smt2cxx -byte-aligned-buffer-elements %s > %t-align.cpp
; RUN: %cxx-rt-syntax %t-align.cpp
; RUN: %FileCheck -check-prefixes CHECK-COMMON,CHECK-ALIGN -input-file=%t-align.cpp %s

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (or a b))
(assert (or b c))
(check-sat)

; CHECK-COMMON: LLVMFuzzerTestOneInput

; CHECK-NO-ALIGN: bool a = makeBoolFrom(jfs_buffer_ref, 0, 0);
; CHECK-NO-ALIGN: const bool b = makeBoolFrom(jfs_buffer_ref, 1, 1);
; CHECK-NO-ALIGN: const bool c = makeBoolFrom(jfs_buffer_ref, 2, 2);

; CHECK-ALIGN: bool a = makeBoolFrom(jfs_buffer_ref, 0, 0);
; CHECK-ALIGN: const bool b = makeBoolFrom(jfs_buffer_ref, 8, 8);
; CHECK-ALIGN: const bool c = makeBoolFrom(jfs_buffer_ref, 16, 16);
