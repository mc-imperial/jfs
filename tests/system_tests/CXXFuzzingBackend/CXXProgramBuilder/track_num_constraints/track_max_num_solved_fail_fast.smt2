; RUN: %jfs-smt2cxx -branch-encoding=fail-fast -record-max-num-satisfied-constraints %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))
(check-sat)

; FIXME: These checks for braces are really fragile.
; CHECK: uint64_t jfs_max_num_const_sat = 0;
; CHECK: extern "C" void LLVMFuzzerAtExit()
; CHECK-NEXT: {
; CHECK-NEXT: jfs_nr_logger_ty logger = jfs_nr_mk_logger_from_env();
; CHECK-NEXT: jfs_nr_log_uint64(logger,"jfs_max_num_const_sat",jfs_max_num_const_sat);
; CHECK-NEXT: jfs_nr_del_logger(logger);
; CHECK-NEXT: }

; CHECK: extern "C" int LLVMFuzzerTestOneInput
; CHECK: bool [[SSA0:[a-z_0-9]+]] = a || b;
; CHECK-NEXT: if ([[SSA0]])
; CHECK-NEXT: {
; CHECK-NEXT: ++jfs_num_const_sat;
; CHECK-NEXT: if (jfs_max_num_const_sat < jfs_num_const_sat)
; CHECK-NEXT: {
; CHECK-NEXT: jfs_max_num_const_sat = jfs_num_const_sat;
; CHECK-NEXT: }
; CHECK-NEXT: }

