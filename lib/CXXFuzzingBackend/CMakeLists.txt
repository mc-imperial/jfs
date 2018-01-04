#===------------------------------------------------------------------------===#
#
#                         JFS - The JIT Fuzzing Solver
#
# Copyright 2017-2018 Daniel Liew
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#
jfs_add_component(JFSCXXFuzzingBackend
  ClangInvocationManager.cpp
  ClangOptions.cpp
  CXXFuzzingSolver.cpp
  CXXFuzzingSolverOptions.cpp
  CXXProgram.cpp
  CXXProgramBuilderPass.cpp
  CXXProgramBuilderPassImpl.cpp
  JFSCXXProgramStat.cpp
)
target_link_libraries(JFSCXXFuzzingBackend PUBLIC JFSFuzzingCommon)

jfs_get_llvm_components(llvm_components support)

target_link_libraries(JFSCXXFuzzingBackend PUBLIC ${llvm_components})

add_subdirectory(CmdLine)
