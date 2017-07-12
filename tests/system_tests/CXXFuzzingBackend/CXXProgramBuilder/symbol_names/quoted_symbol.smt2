; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun |abcFOO! | () Bool)
(declare-fun |abcFOO! @| () Bool)
(assert (or |abcFOO! | |abcFOO! @|))
; CHECK:  bool abcFOO_ex__ = makeBoolFrom
; CHECK:  bool abcFOO_ex___at_ = makeBoolFrom
(check-sat)
