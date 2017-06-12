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


option(BUILD_RUNTIME_TESTS_WITH_RUNTIME_COMPILER
  "Build runtime tests with runtime compiler"
  ON
)

if (BUILD_RUNTIME_TESTS_WITH_RUNTIME_COMPILER)
  # The runtime tests are built as an external project
  # so that we can use the runtime compiler rather than
  # the host compiler.
  include(ExternalProject)
  option(BUILD_RUNTIME_TESTS_WITH_UBSAN "Build runtime tests with UBSan" ON)
  option(BUILD_RUNTIME_TESTS_WITH_ASAN "Build runtime tests with ASan" ON)
  # TODO: Validate this option is Release, Debug, or RelWithDebInfo
  set(RUNTIME_TEST_BUILD_TYPE "RelWithDebInfo" CACHE STRING "Runtime test build type")
  message(STATUS "Building runtime tests with runtime compiler")

  ExternalProject_Add(SMTLIBRuntimeTests
    SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/SMTLIBRuntime"
    # FIXME: We should allow other generators
    CMAKE_GENERATOR "Unix Makefiles"
    CMAKE_ARGS
      "-DCMAKE_CXX_COMPILER=${LLVM_CLANG_CXX_TOOL}"
      "-DJFS_SRC_ROOT=${CMAKE_SOURCE_DIR}"
      "-DJFS_BINARY_ROOT=${CMAKE_BINARY_DIR}"
      "-DGTEST_SRC_DIR=${GTEST_SRC_DIR}"
      "-DUSE_UBSAN=${BUILD_RUNTIME_TESTS_WITH_UBSAN}"
      "-DUSE_ASAN=${BUILD_RUNTIME_TESTS_WITH_ASAN}"
      "-DCMAKE_BUILD_TYPE=${RUNTIME_TEST_BUILD_TYPE}"
    BINARY_DIR "${CMAKE_CURRENT_BINARY_DIR}/SMTLIBRuntime"
    BUILD_ALWAYS 1
    # HACK: This hack means that if the build generator for JFS
    # is Make then `-j` value will passed through to make run
    # to build the external project.
    # See
    # http://cmake.3232098.n2.nabble.com/How-would-I-use-parallel-make-on-ExternalProjects-td5609078.html
    #
    # We should remove this, or at the very least guard it based on the
    # current generator.
    BUILD_COMMAND "$(MAKE)"
    # Don't run install command
    INSTALL_COMMAND ""
    # FIXME: Guard these based on CMake version
    USES_TERMINAL_BUILD 1
    USES_TERMINAL_CONFIGURE 1
  )

  # For the makefile generator clean up after the external project
  set_property(DIRECTORY
    "${CMAKE_CURRENT_SOURCE_DIR}"
    PROPERTY
    ADDITIONAL_MAKE_CLEAN_FILES
    "${CMAKE_CURRENT_BINARY_DIR}/SMTLIBRuntime"
    # FIXME: This is a hack and implementational detail of the external project
    "${CMAKE_BINARY_DIR}/utils/googletest_runtime"
  )
else()
  message(STATUS "Building runtime tests with host compiler")
  add_subdirectory(SMTLIBRuntime/BitVector)
endif()
