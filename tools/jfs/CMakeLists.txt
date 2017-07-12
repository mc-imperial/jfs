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
add_executable(jfs_tool
  main.cpp
)

# Needed for command line support
jfs_get_llvm_components(llvm_components support)

target_link_libraries(
  jfs_tool
  PRIVATE
  ${llvm_components}
  JFSSupport
  JFSCore
  JFSTransform
  JFSFuzzingCommon
  JFSZ3Backend
  JFSCXXFuzzingBackend
  JFSCXXFuzzingBackendCmdLine
)

# Give shortname
set_property(TARGET jfs_tool PROPERTY OUTPUT_NAME jfs)
