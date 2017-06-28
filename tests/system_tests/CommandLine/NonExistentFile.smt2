; RUN: %not %jfs NON_EXISTANT_FILE 2>&1 | %FileCheck %s
; CHECK: (error "Could not open NON_EXISTANT_FILE because No such file or directory")
