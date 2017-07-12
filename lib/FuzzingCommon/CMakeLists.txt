#===------------------------------------------------------------------------===#
#
#                         JFS - The JIT Fuzzing Solver
#
# Copyright 2017 Daniel Liew
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#
jfs_add_component(JFSFuzzingCommon
  CommandLineCategory.cpp
  DummyFuzzingSolver.cpp
  EqualityExtractionPass.cpp
  FreeVariableToBufferAssignmentPass.cpp
  FuzzingSolver.cpp
  FuzzingAnalysisInfo.cpp
  LibFuzzerInvocationManager.cpp
  LibFuzzerOptions.cpp
  SortConformanceCheckPass.cpp
  WorkingDirectoryManager.cpp
)
target_link_libraries(JFSFuzzingCommon
  PUBLIC
  JFSTransform
  JFSCore
  JFSSupport
)

add_subdirectory(CmdLine)
