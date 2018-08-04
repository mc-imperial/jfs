; RUN: rm -f %t-stats.yml
; RUN: %jfs -cxx --branch-encoding=fail-fast --disable-equality-extraction --disable-standard-passes -libfuzzer-runs=100 -seed=1  -stats-file=%t-stats.yml -record-max-num-satisfied-constraints %s | %FileCheck -check-prefix=CHECK-SAT %s
; RUN: %yaml-syntax-check %t-stats.yml
; RUN: %FileCheck -check-prefix=CHECK-STATS -input-file=%t-stats.yml %s
; CHECK-SAT: {{^unknown}}

; CHECK-STATS
; CHECK-STATS: name: CXXProgramBuilderPassImpl
; CHECK-STATS-NEXT: num_constraints: 3
; CHECK-STATS: name: runtime_fuzzing_stats
; CHECK-STATS-NEXT: jfs_max_num_const_sat: 2
; NOTE: These stats below are technically wrong. They show as zero because they
; aren't tracked in this test.
; CHECK-STATS-NEXT: jfs_num_inputs: 0
; CHECK-STATS-NEXT: jfs_num_wrong_size_inputs: 0



(set-logic QF_BV)
(set-info :smt-lib-version 2.5)
(set-info :status unsat)
(declare-const a Bool)
(declare-const b Bool)
(declare-const c Bool)
(assert (and a b)) ; Should be satisfied
(assert (xor b c)) ; Should be satisfied
(assert c) ; can't be satisfied. The fuzzer should get stuck here
(check-sat)
(exit)
