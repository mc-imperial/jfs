; RUN: %jfs-smt2cxx -branch-encoding=fail-fast -record-max-num-satisfied-constraints=0 -record-num-inputs=0 %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (or a b))
(assert (or b c))
(check-sat)

; FIXME: These checks for braces are really fragile.

; CHECK: LLVMFuzzerTestOneInput(const uint8_t* data, size_t size)
; CHECK-NEXT: {

; CHECK: const bool jfs_ssa_0 = a || b;
; CHECK-NEXT: if (jfs_ssa_0) {}
; CHECK-NEXT: else {
; CHECK-NEXT: return 0;
; CHECK-NEXT: }

; CHECK: const bool jfs_ssa_1 = b || c;
; CHECK-NEXT: if (jfs_ssa_1) {}
; CHECK-NEXT: else {
; CHECK-NEXT: return 0;
; CHECK-NEXT: }

; CHECK:// Fuzzing target
; CHECK-NEXT: abort();

; CHECK: }
