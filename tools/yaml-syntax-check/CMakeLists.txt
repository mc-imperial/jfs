
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
add_executable(yaml_syntax_check
  main.cpp
)

# Needed for command line support
jfs_get_llvm_components(llvm_components support)
target_link_libraries(yaml_syntax_check
  PRIVATE
  ${llvm_components}
  JFSSupport # HACK: Not really needed but this will give us the compiler flags
)
