; RUN: %jfs-smt2cxx -byte-aligned-buffer-elements=false %s > %t-no-align.cpp
; RUN: %cxx-rt-syntax %t-no-align.cpp
; RUN: %FileCheck -check-prefixes CHECK-COMMON,CHECK-NO-ALIGN -input-file=%t-no-align.cpp %s
; RUN: %jfs-smt2cxx -byte-aligned-buffer-elements %s > %t-align.cpp
; RUN: %cxx-rt-syntax %t-align.cpp
; RUN: %FileCheck -check-prefixes CHECK-COMMON,CHECK-ALIGN -input-file=%t-align.cpp %s

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () (_ BitVec 2))
(declare-fun e () (_ BitVec 19))
(assert (or a b))
(assert (bvult d #b11))
(assert (bvult e #b1010101010101001011))
(assert (or b c))
(check-sat)

; CHECK-COMMON: LLVMFuzzerTestOneInput

; CHECK-NO-ALIGN: bool a = makeBoolFrom(jfs_buffer_ref, 0, 0);
; CHECK-NO-ALIGN: bool b = makeBoolFrom(jfs_buffer_ref, 1, 1);
; CHECK-NO-ALIGN: BitVector<2> d = makeBitVectorFrom<2>(jfs_buffer_ref, 2, 3);
; CHECK-NO-ALIGN: BitVector<19> e = makeBitVectorFrom<19>(jfs_buffer_ref, 4, 22);
; CHECK-NO-ALIGN: bool c = makeBoolFrom(jfs_buffer_ref, 23, 23);


; CHECK-ALIGN: bool a = makeBoolFrom(jfs_buffer_ref, 0, 0);
; CHECK-ALIGN: bool b = makeBoolFrom(jfs_buffer_ref, 8, 8);
; CHECK-ALIGN: BitVector<2> d = makeBitVectorFrom<2>(jfs_buffer_ref, 16, 17);
; CHECK-ALIGN: BitVector<19> e = makeBitVectorFrom<19>(jfs_buffer_ref, 24, 42);
; CHECK-ALIGN: bool c = makeBoolFrom(jfs_buffer_ref, 48, 48);
