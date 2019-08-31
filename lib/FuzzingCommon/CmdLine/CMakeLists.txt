#===------------------------------------------------------------------------===#
#
#                                      JFS
#
# Copyright 2017-2018 Daniel Liew
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#
jfs_add_component(JFSFuzzingCommonCmdLine
  FreeVariableToBufferAssignmentPassOptionsBuilder.cpp
  LibFuzzerOptionsBuilder.cpp
  SeedManagerOptionsBuilder.cpp
)
target_link_libraries(JFSFuzzingCommonCmdLine
  PUBLIC
  JFSFuzzingCommon
)
jfs_get_llvm_components(llvm_components support)

target_link_libraries(JFSFuzzingCommonCmdLine PUBLIC ${llvm_components})
