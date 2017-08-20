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
# This is a simple wrapper around the GTest CMake build that
# exports its targets. The purpose of this is so this file can
# be used as the root CMakeLists.txt of an external project build.
project(GTEST_WRAPPER)
cmake_minimum_required(VERSION 2.6.2)

if (NOT EXISTS "${GTEST_SRC_DIR}")
  message(FATAL_ERROR "GTEST_SRC_DIR \"${GTEST_SRC_DIR}\" does not exist")
endif()

add_subdirectory(
  "${GTEST_SRC_DIR}"
  "${CMAKE_CURRENT_BINARY_DIR}/gtest_build"
)

set(JFS_GTEST_EXPORT_FILE "${CMAKE_CURRENT_BINARY_DIR}/jfs_gtest_exported_targets.cmake")
# Export the gtest targets so that other external projects can re-use the build
export(TARGETS jfs_gtest_main jfs_gtest
  FILE "${JFS_GTEST_EXPORT_FILE}"
  EXPORT_LINK_INTERFACE_LIBRARIES
)
