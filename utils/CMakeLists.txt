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

###############################################################################
# Build LLVM testing tools
###############################################################################
add_subdirectory(FileCheck)
add_subdirectory(not)

###############################################################################
# Build GTest
###############################################################################
add_subdirectory(
  "${GTEST_SRC_DIR}"
  "${CMAKE_BINARY_DIR}/utils/googletest"
)

set(JFS_GTEST_EXPORT_FILE "${CMAKE_CURRENT_BINARY_DIR}/jfs_gtest_exported_targets.cmake")
# Export the gtest targets so that other external projects can re-use the build
export(TARGETS jfs_gtest_main jfs_gtest
  FILE "${JFS_GTEST_EXPORT_FILE}"
  EXPORT_LINK_INTERFACE_LIBRARIES
)
# Export to parent scope so users don't have to hardcode the path
set(JFS_GTEST_EXPORT_FILE "${JFS_GTEST_EXPORT_FILE}" PARENT_SCOPE)
