; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun abc^ABC0123 () Bool)
(declare-fun abc^^ABC0123 () Bool)
(assert (or abc^ABC0123 abc^^ABC0123))
; CHECK:  bool abc_c_ABC0123 = makeBoolFrom
; CHECK:  bool abc_c__c_ABC0123 = makeBoolFrom
(check-sat)
