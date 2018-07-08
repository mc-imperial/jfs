; NOTE: try-all-imncsf uses an experimental LibFuzzer feature (custom counters)
; which currently only works on Linux.
; REQUIRES: linux
; RUN: %jfs-smt2cxx -branch-encoding=try-all-imncsf %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
; RUN: %FileCheck -check-prefix=PASS -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (or a b))
(assert (or b c))
(check-sat)

; PASS-NOT: extern "C" void LLVMFuzzerAtExit()

; FIXME: These checks for braces are really fragile.
; CHECK: uint64_t jfs_max_num_const_sat = 0;

; CHECK: #ifdef __linux__
; CHECK-NEXT: __attribute__((section("__libfuzzer_extra_counters")))
; CHECK-NEXT: #endif
; CHECK-NEXT: static uint8_t jfs_libfuzzer_custom_counter[2];


; CHECK: LLVMFuzzerTestOneInput(const uint8_t* data, size_t size)
; CHECK-NEXT: {

; CHECK: uint64_t jfs_num_const_sat = 0;
; CHECK: const bool jfs_ssa_0 = a || b;
; CHECK-NEXT: if (jfs_ssa_0)
; CHECK-NEXT: {
; CHECK-NEXT:   ++jfs_num_const_sat;
; CHECK-NEXT: }

; CHECK: const bool jfs_ssa_1 = b || c;
; CHECK-NEXT: if (jfs_ssa_1)
; CHECK-NEXT: {
; CHECK-NEXT:   ++jfs_num_const_sat;
; CHECK-NEXT: }

; CHECK-NEXT: if (jfs_max_num_const_sat < jfs_num_const_sat)
; CHECK-NEXT: {
; CHECK-NEXT:   jfs_max_num_const_sat = jfs_num_const_sat;
; CHECK-NEXT: }

; CHECK-NEXT: if (jfs_max_num_const_sat > 0)
; CHECK-NEXT: {
; CHECK-NEXT:   jfs_libfuzzer_custom_counter[jfs_max_num_const_sat -1] = 1;
; CHECK-NEXT: }

; CHECK:      if (jfs_num_const_sat == 2)
; CHECK-NEXT: {
; CHECK-NEXT:   // Fuzzing target
; CHECK-NEXT:   abort();
; CHECK-NEXT: }
; CHECK-NEXT: else {
; CHECK-NEXT:   return 0;
; CHECK-NEXT: }

; CHECK: }
