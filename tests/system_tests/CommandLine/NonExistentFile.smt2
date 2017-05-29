; RUN: %not %jfs NON_EXISTANT_FILE 2>&1 | %FileCheck %s
; CHECK: (error "NON_EXISTANT_FILE does not exist")
