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
project(SMTLIBRuntime CXX)

###############################################################################
# Minimum CMake version and policies
###############################################################################
cmake_minimum_required(VERSION 2.8.12)

if (NOT DEFINED JFS_SRC_ROOT)
  message(FATAL_ERROR "JFS_SRC_ROOT must be defined")
endif()
if (NOT EXISTS "${JFS_SRC_ROOT}")
  message(FATAL_ERROR "JFS_SRC_ROOT (${JFS_SRC_ROOT}) must exist")
endif()

if (NOT DEFINED JFS_BINARY_ROOT)
  message(FATAL_ERROR "JFS_BINARY_ROOT must be defined")
endif()
if (NOT EXISTS "${JFS_BINARY_ROOT}")
  message(FATAL_ERROR "JFS_BINARY_ROOT (${JFS_BINARY_ROOT}) must exist")
endif()

if (NOT EXISTS "${GTEST_SRC_DIR}")
  message(FATAL_ERROR "GTEST_SRC_DIR (${GTEST_SRC_DIR}) must exist")
endif()

###############################################################################
# Language version
###############################################################################
include(CheckCXXCompilerFlag)
CHECK_CXX_COMPILER_FLAG("-std=c++11" HAS_CXX_11_FLAG)

# We should use C++11
if (HAS_CXX_11_FLAG)
  string(APPEND CMAKE_CXX_FLAGS " -std=c++11")
else()
  message(FATAL_ERROR "Compiler does not support C++11")
endif()
message(STATUS "Using CXX compiler : ${CMAKE_CXX_COMPILER}")

###############################################################################
# Sanitizer support
###############################################################################
OPTION(USE_UBSAN "Build with UBSan" OFF)
if (USE_UBSAN)
  message(STATUS "Building with UBSan")
  string(APPEND CMAKE_CXX_FLAGS " -fsanitize=undefined -fno-omit-frame-pointer")
else()
  message(STATUS "Not building with UBSan")
endif()

OPTION(USE_ASAN "Build with ASan" OFF)
if (USE_ASAN)
  message(STATUS "Building with ASan")
  string(APPEND CMAKE_CXX_FLAGS " -fsanitize=address -fno-omit-frame-pointer")
else()
  message(STATUS "Not building with ASan")
endif()

###############################################################################
# Header only library
###############################################################################

add_library(JFSSMTLIBRuntime INTERFACE)

target_include_directories(JFSSMTLIBRuntime
  INTERFACE "${JFS_BINARY_ROOT}/runtime/include"
)

# Header should use C++11
target_compile_options(JFSSMTLIBRuntime
  INTERFACE "${JFS_USE_CXX_FLAG}"
)

# Runtime asserts
option(ENABLE_JFS_RUNTIME_ASSERTS "Enable runtime assertions" ON)
if (ENABLE_JFS_RUNTIME_ASSERTS)
  message(STATUS "JFS runtime asserts enabled")
  target_compile_definitions(JFSSMTLIBRuntime
    INTERFACE
    "-DJFS_RUNTIME_FAILURE_CALLS_ABORT"
    "-DENABLE_JFS_RUNTIME_ASSERTS"
  )
else()
  message(STATUS "JFS runtime asserts disabled")
endif()

###############################################################################
# Utility library
###############################################################################
add_library(JFSSMTLIBRuntimeTestUtil
  SMTLIBRuntimeTestUtil.cpp
)
target_include_directories(JFSSMTLIBRuntimeTestUtil
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
)

###############################################################################
# Build GTest
###############################################################################
# FIXME: This is kind of wasteful. We should import the targets instead and just
# reuse them.
# Build gtest
add_subdirectory(
  "${GTEST_SRC_DIR}"
  # FIXME: This is a horrible hack.
  # Build outside of our binary tree so that lit doesn't pick up binaries
  "${JFS_BINARY_ROOT}/utils/googletest_runtime"
)

###############################################################################
# Declare unit tests
###############################################################################
include("${JFS_SRC_ROOT}/cmake/add_jfs_unit_test.cmake")

add_subdirectory(BitVector)
add_subdirectory(Core)
