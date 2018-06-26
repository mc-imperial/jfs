#===------------------------------------------------------------------------===#
#
#                         JFS - The JIT Fuzzing Solver
#
# Copyright 2018 J. Ryan Stinnett
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#
add_executable(jfs-smt2cnf
  main.cpp
)

# Needed for command line support
jfs_get_llvm_components(llvm_components support)

target_link_libraries(
  jfs-smt2cnf
  PRIVATE
  ${llvm_components}
  JFSSupport
  JFSCXXFuzzingBackendCmdLine
  JFSCXXFuzzingBackend
  JFSFuzzingCommonCmdLine
)
