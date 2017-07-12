; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun abcABC0123 () Bool)
(declare-fun abcABC0124 () Bool)
(assert (or abcABC0123 abcABC0124))
; CHECK:  bool abcABC0123 = makeBoolFrom
; CHECK:  bool abcABC0124 = makeBoolFrom
(check-sat)
