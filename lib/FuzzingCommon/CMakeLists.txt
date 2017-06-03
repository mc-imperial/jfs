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
  DummyFuzzingSolver.cpp
  FuzzingSolver.cpp
)
target_link_libraries(JFSFuzzingCommon
  PUBLIC
  JFSTransform
  JFSCore
)
