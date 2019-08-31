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
add_executable(jfs-opt
  main.cpp
)

# Needed for command line support
jfs_get_llvm_components(llvm_components support)

target_link_libraries(
  jfs-opt
  PRIVATE
  ${llvm_components}
  JFSSupport
  JFSCore
  JFSTransform
)

