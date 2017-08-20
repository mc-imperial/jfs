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
