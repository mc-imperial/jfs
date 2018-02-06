; RUN: rm -f %t-stats.yml
; FIXME: When we allow different encodings make sure that we specify the fail fast encoding here.
; FIXME: This test is kind of racey. We want the time to be long enough that fuzzing occurs but
; not so long that testing becomes too slow. We should add an option to just do a fix number of
; of fuzzing runs to avoid this.
; RUN: %jfs -cxx --disable-standard-passes -max-time=3 -stats-file=%t-stats.yml -record-max-num-satisfied-constraints %s | %FileCheck -check-prefix=CHECK-SAT %s
; RUN: %yaml-syntax-check %t-stats.yml
; RUN: %FileCheck -check-prefix=CHECK-STATS -input-file=%t-stats.yml %s
; CHECK-SAT: {{^unknown}}

; FIXME: The reason for these number of constraints is due to equality
; extraction. There's currently no flag to disable this. We should add one
; and fix this.
; CHECK-STATS
; CHECK-STATS: name: CXXProgramBuilderPassImpl
; CHECK-STATS-NEXT: num_constraints: 2
; CHECK-STATS: name: runtime_fuzzing_stats
; CHECK-STATS-NEXT: jfs_max_num_const_sat: 1


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
