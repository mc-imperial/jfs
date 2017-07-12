; RUN: %jfs-smt2cxx %s > %t.cpp
; RUN: %cxx-rt-syntax %t.cpp
; RUN: %FileCheck -input-file=%t.cpp %s
(declare-fun abc-ABC0123 () Bool)
(declare-fun abc_m_ABC0123 () Bool) ; This name deliberately causes a clash
(declare-fun abc-ABC0123_0 () Bool) ; This name deliberately causes a clash
(assert (or abc-ABC0123 abc-ABC0123_0 abc_m_ABC0123))
; CHECK:  bool abc_m_ABC0123 = makeBoolFrom
; CHECK:  bool abc_m_ABC0123_0 = makeBoolFrom
; CHECK:  bool abc_m_ABC0123_1 = makeBoolFrom
(check-sat)
