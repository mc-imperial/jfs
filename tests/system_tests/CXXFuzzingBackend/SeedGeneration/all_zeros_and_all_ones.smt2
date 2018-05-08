; RUN: rm -rf %t.output-dir
; RUN: %jfs -cxx -keep-output-dir -output-dir=%t.output-dir -sm-all-ones-seed -sm-all-zeros-seed -sm-max-num-seed=2 -debug-stop-after-seed-gen -disable-equality-extraction %s

; Check the seeds are exactly what we expect
; FIXME: This sucks. llvm-lit now has a built-in diff but it misbehaves
; on binary files and doesn't support many standard flags. Hack this
; for now by running the diff binary explicitly
; RUN: %diff -q %t.output-dir/corpus/zeros_0 %S/3b_all_zeros
; RUN: %diff -q %t.output-dir/corpus/ones_0 %S/3b_all_ones
; FIXME: We should probably come up with a more elegant way of doing this.
; RUN: ls %t.output-dir/corpus | wc -l | grep '^\s*2$'


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
