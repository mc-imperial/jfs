; RUN: %jfs-smt2cxx -record-num-wrong-sized-inputs %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun a () Bool)
(declare-fun b () Bool)
(assert (or a b))
(check-sat)

; FIXME: These checks for braces are really fragile.
; CHECK: uint64_t jfs_num_wrong_size_inputs = 0;
; CHECK: extern "C" void LLVMFuzzerAtExit()
; CHECK-NEXT: {
; CHECK-NEXT: jfs_nr_logger_ty logger = jfs_nr_mk_logger_from_env();
; CHECK-NEXT: jfs_nr_log_uint64(logger,"jfs_num_wrong_size_inputs",jfs_num_wrong_size_inputs);
; CHECK-NEXT: jfs_nr_del_logger(logger);
; CHECK-NEXT: }

; CHECK: extern "C" int LLVMFuzzerTestOneInput
; CHECK-NEXT: {
; CHECK-NEXT: if (size != 1)
; CHECK-NEXT: {
; CHECK-NEXT: ++jfs_num_wrong_size_inputs;
; CHECK-NEXT: jfs_warning("Wrong sized input tried.\n");
; CHECK-NEXT: return 0;
; CHECK-NEXT: }
