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

if (NOT DEFINED JFS_SOURCE_ROOT)
  message(FATAL_ERROR "JFS_SOURCE_ROOT must be defined")
endif()
if (NOT EXISTS "${JFS_SOURCE_ROOT}")
  message(FATAL_ERROR "JFS_SOURCE_ROOT (${JFS_SOURCE_ROOT}) must exist")
endif()

if (NOT DEFINED JFS_BINARY_ROOT)
  message(FATAL_ERROR "JFS_BINARY_ROOT must be defined")
endif()
if (NOT EXISTS "${JFS_BINARY_ROOT}")
  message(FATAL_ERROR "JFS_BINARY_ROOT (${JFS_BINARY_ROOT}) must exist")
endif()

if (NOT DEFINED JFS_GTEST_EXPORT_FILE)
  message(FATAL_ERROR "JFS_GTEST_EXPORT_FILE must be defined")
endif()

if (NOT DEFINED LIT_TOOL)
  message(FATAL_ERROR "LIT_TOOL must be defined")
else()
  message(STATUS "LIT_TOOL: \"${LIT_TOOL}\"")
endif()

if (NOT DEFINED LIT_ARGS)
  message(FATAL_ERROR "LIT_ARGS must be defined")
else()
  message(STATUS "LIT_ARGS: \"${LIT_ARGS}\"")
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
# SMTLIB runtime
###############################################################################

add_library(JFSSMTLIBRuntime
  STATIC
  Core.cpp
  NativeBitVector.cpp
)

# FIXME: We shouldn't be relying on external to set this up.
target_include_directories(JFSSMTLIBRuntime
  PUBLIC "${JFS_BINARY_ROOT}/runtime/include"
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
    PUBLIC
    "-DENABLE_JFS_RUNTIME_ASSERTS"
  )
else()
  message(STATUS "JFS runtime asserts disabled")
endif()

option(JFS_RUNTIME_ASSERTS_CALL_ABORT "JFS runtime asserts call abort on failure" OFF)
if (JFS_RUNTIME_ASSERTS_CALL_ABORT)
  message(STATUS "JFS runtime asserts call abort()")
  target_compile_definitions(JFSSMTLIBRuntime
    PUBLIC
    "-DJFS_RUNTIME_FAILURE_CALLS_ABORT"
  )
endif()

###############################################################################
# Unit tests
###############################################################################
option(ENABLE_UNIT_TESTS "Enable unit tests" ON)
if (ENABLE_UNIT_TESTS)
  add_subdirectory(unittests)
endif()
