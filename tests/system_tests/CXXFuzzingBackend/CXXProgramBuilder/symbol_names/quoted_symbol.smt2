; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun |abcFOO! | () Bool)
(declare-fun |abcFOO! @| () Bool)
(assert (or |abcFOO! | |abcFOO! @|))
; CHECK:  bool abc_fs_ABC0123 = makeBoolFrom
; CHECK:  bool abc_fs__fs_ABC0123 = makeBoolFrom
(check-sat)
