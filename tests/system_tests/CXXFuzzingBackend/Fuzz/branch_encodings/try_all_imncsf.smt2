; NOTE: try-all-imncsf uses an experimental LibFuzzer feature (custom counters)
; which currently only works on Linux.
; REQUIRES: linux && LibFuzzer
; RUN: rm -rf %t-output-dir
; RUN: %jfs -branch-encoding=try-all-imncsf -cxx -disable-equality-extraction -disable-standard-passes -keep-output-dir -output-dir=%t-output-dir %s | %FileCheck %s

; RUN: %FileCheck -check-prefix=CHECK-LIBFUZZER -input-file=%t-output-dir/libfuzzer.stderr.txt %s

; NOTE: This output is not part of upstream LibFuzzer.
; CHECK-LIBFUZZER: INFO: 16 Extra Counters


(set-logic QF_BV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.

|)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun buffer_0 () (_ BitVec 8))
(declare-fun buffer_1 () (_ BitVec 8))
(declare-fun buffer_2 () (_ BitVec 8))
(assert (not (= ((_ sign_extend 24) buffer_0) (_ bv0 32))))
(assert (not (= ((_ sign_extend 24) buffer_0) (_ bv43 32))))
(assert (= ((_ sign_extend 24) buffer_0) (_ bv37 32)))
(assert (not (= ((_ sign_extend 24) buffer_1) (_ bv0 32))))
(assert (not (= ((_ sign_extend 24) buffer_1) (_ bv37 32))))
(assert (not (= ((_ sign_extend 24) buffer_1) (_ bv45 32))))
(assert (not (= ((_ sign_extend 24) buffer_1) (_ bv48 32))))
(assert (bvsle (_ bv48 32) ((_ sign_extend 24) buffer_1)))
(assert (bvsle ((_ sign_extend 24) buffer_1) (_ bv57 32)))
(assert (bvsle (_ bv48 32) ((_ sign_extend 24) buffer_2)))
(assert (not (bvsle ((_ sign_extend 24) buffer_2) (_ bv57 32))))
(assert (not (= ((_ sign_extend 24) buffer_2) (_ bv115 32))))
(assert (not (= ((_ sign_extend 24) buffer_2) (_ bv100 32))))
(assert (= ((_ sign_extend 24) buffer_2) (_ bv120 32)))
(assert (not (bvsle (bvadd (_ bv0 32) (bvadd ((_ sign_extend 24) buffer_1) (bvneg (_ bv48 32)))) (_ bv7 32))))
(assert (not (bvslt (_ bv0 32) (bvadd (bvadd (bvadd (_ bv0 32) (bvadd ((_ sign_extend 24) buffer_1) (bvneg (_ bv48 32)))) (bvneg (_ bv7 32))) (bvneg (_ bv1 32))))))
(check-sat)
; CHECK: {{^sat$}}
(exit)
