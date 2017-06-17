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
jfs_add_component(JFSCXXFuzzingBackend
  CXXFuzzingSolver.cpp
  CXXProgram.cpp
  CXXProgramBuilderPass.cpp
)
target_link_libraries(JFSCXXFuzzingBackend PUBLIC JFSFuzzingCommon)
