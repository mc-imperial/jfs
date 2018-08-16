; RUN: rm -f %t.stats.yml
; RUN: %jfs -v=2 \
; RUN: -stats-file=%t.stats.yml \
; RUN: -sm-all-ones-seed=0 \
; RUN: -sm-all-zeros-seed=0 \
; RUN: -sm-special-constant-seeds=true \
; RUN: -sm-max-num-seed=9 %s | %FileCheck -check-prefix=CHECK-SAT %s
; RUN: %yaml-syntax-check %t.stats.yml
; RUN: %FileCheck %s -check-prefix=CHECK-STATS -input-file=%t.stats.yml

(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () (_ BitVec 2))
(declare-fun e () (_ BitVec 19))
(declare-fun f () Float32)
(declare-fun g () Float64)
(assert (or a b))
(assert (bvult d #b11))
(assert (bvult e #b1010101010101001011))
(assert (fp.eq f f))
(assert (fp.eq g g))
(assert (or b c))
(check-sat)

; CHECK-SAT: {{^sat}}

; CHECK-STATS: name: special_constant_seed_generator
; CHECK-STATS: total_built_in_bv_constants: 4
; CHECK-STATS: num_covered_built_in_bv_constant: {{[1-4]}}
; CHECK-STATS: total_built_in_fp_constants: 15
; CHECK-STATS: num_covered_built_in_fp_constant: {{[1-9]+}}
; CHECK-STATS: total_built_in_bool_constants: 2
; CHECK-STATS: num_covered_built_in_bv_constant: 2
; CHECK-STATS: num_constants_by_sort:
; CHECK-STATS-NEXT:   "(_ BitVec 19)": 1
; CHECK-STATS-NEXT:   "(_ BitVec 2)": 1

