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

# TODO: This copy should be moved into the external project
file(MAKE_DIRECTORY "${CMAKE_BINARY_DIR}/runtime/include")
file(MAKE_DIRECTORY "${CMAKE_BINARY_DIR}/runtime/include/SMTLIB")
set(RUNTIME_HEADERS
  "BitVector.h"
  "BufferRef.h"
  "Core.h"
  "NativeBitVector.h"
  "jassert.h"
)
foreach (runtime_header ${RUNTIME_HEADERS})
  # Use configure_file() so that changes to the files in the source tree
  # trigger CMake to re-configure itself which will then cause the copies
  # of the headers in the build tree to be updated.
  configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/SMTLIB/${runtime_header}"
    "${CMAKE_BINARY_DIR}/runtime/include/SMTLIB/${runtime_header}"
    COPYONLY
  )
endforeach()

# Build runtime as external project. This allows us to use a different
# compiler from the host and also build multiple variants of the runtime.
include(ExternalProject)
include(CMakeParseArguments)
include(${CMAKE_SOURCE_DIR}/cmake/jfs_external_project_utils.cmake)

# Properties populated by the `AddJFSRuntimeBuild()` macro.
# They need to be global properties so that they can be consumed from
# other parts of the build system
define_property(
  GLOBAL
  PROPERTY
  JFS_AVAILABLE_RUNTIMES
  BRIEF_DOCS "List of available JFS runtimes"
  FULL_DOCS "List of available JFS runtimes"
)
define_property(
  GLOBAL
  PROPERTY
  JFS_STATIC_RUNTIME_PATH
  BRIEF_DOCS "List of JFS static runtime library paths relative to runtime directory"
  FULL_DOCS "List of JFS static runtime library paths relative to runtime directory"
)

macro(AddJFSRuntimeBuild)
  cmake_parse_arguments(jfs_runtime_arg
    "ASAN;UBSAN;RUNTIME_ASSERTS;DEBUG_SYMBOLS;OPTIMIZED;RUN_UNIT_TESTS"
    ""
    ""
    ${ARGN}
  )
  # Compute build name from arguments
  set(buildName "")
  if (jfs_runtime_arg_DEBUG_SYMBOLS)
    string(APPEND buildName "_DebugSymbols")
  endif()
  if (jfs_runtime_arg_OPTIMIZED)
    string(APPEND buildName "_Optimized")
  endif()
  if (jfs_runtime_arg_RUNTIME_ASSERTS)
    string(APPEND buildName "_RuntimeAsserts")
  endif()
  if (jfs_runtime_arg_ASAN)
    string(APPEND buildName "_ASan")
  endif()
  if (jfs_runtime_arg_UBSAN)
    string(APPEND buildName "_UBSan")
  endif()
  message(STATUS "Adding JFS runtime ${buildName}")
  set(buildDir "${CMAKE_CURRENT_BINARY_DIR}/SMTLIB_${buildName}")

  # Compute CMake build type
  if (jfs_runtime_arg_OPTIMIZED)
    if (jfs_runtime_arg_DEBUG_SYMBOLS)
      set(jfs_runtime_cmake_build_type "RelWithDebInfo")
    else()
      set(jfs_runtime_cmake_build_type "Release")
    endif()
  else()
    set(jfs_runtime_cmake_build_type "Debug")
  endif()

  jfs_get_external_project_build_command(JFS_EXTERNAL_PROJECT_BUILD_COMMAND ${buildDir})
  set(external_project_target_name "BuildSMTLIBRuntime${buildName}")
  ExternalProject_Add(${external_project_target_name}
    DEPENDS jfs_gtest_main jfs_gtest
    SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/SMTLIB"
    # FIXME: We should allow other generators
    CMAKE_GENERATOR "Unix Makefiles"
    CMAKE_ARGS
      "-DCMAKE_CXX_COMPILER=${LLVM_CLANG_CXX_TOOL}"
      "-DCMAKE_BUILD_TYPE=${jfs_runtime_cmake_build_type}"
      "-DJFS_BINARY_ROOT=${CMAKE_BINARY_DIR}"
      "-DJFS_SOURCE_ROOT=${CMAKE_SOURCE_DIR}"
      "-DJFS_GTEST_EXPORT_FILE=${JFS_GTEST_EXPORT_FILE}"
      "-DGTEST_SRC_DIR=${GTEST_SRC_DIR}"
      "-DLIT_TOOL:string=${LIT_TOOL}"
      "-DUSE_ASAN=${jfs_runtime_arg_ASAN}"
      "-DUSE_UBSAN=${jfs_runtime_arg_UBSAN}"
      "-DENABLE_JFS_RUNTIME_ASSERTS=${jfs_runtime_arg_RUNTIME_ASSERTS}"
      "-DJFS_RUNTIME_ASSERTS_CALL_ABORT=OFF"
    CMAKE_CACHE_ARGS
      # HACK: We have to pass `LIT_ARGS` this way because
      # its a list and passing it in `CMAKE_ARGS` doesn't
      # seem to work.
      "-DLIT_ARGS:string=${LIT_ARGS}"
      "-DENABLE_UNIT_TESTS:bool=${jfs_runtime_arg_RUN_UNIT_TESTS}"
    BINARY_DIR "${buildDir}"
    BUILD_ALWAYS 1
    ${JFS_EXTERNAL_PROJECT_BUILD_COMMAND}
    # Don't run install command
    INSTALL_COMMAND ""
    # FIXME: Guard these based on CMake version
    USES_TERMINAL_BUILD 1
    USES_TERMINAL_CONFIGURE 1
  )
  if (jfs_runtime_arg_RUN_UNIT_TESTS)
    message(STATUS "Enabling unit tests for JFS runtime ${buildName}")
    # Add custom target that invokes the unit teset target inside the external project
    add_custom_target(jfs_runtime_${buildName}_unittests
      COMMENT "Runing JFS ${buildName} Runtime unittests"
      COMMAND
      "${CMAKE_COMMAND}" --build "${buildDir}/unittests" --target jfs_runtime_unittests
      DEPENDS ${external_project_target_name}
      USES_TERMINAL
    )
    add_dependencies(unittests jfs_runtime_${buildName}_unittests)
  endif()

  # Append to JFS_AVAILABLE_RUNTIMES
  string(TOUPPER "${buildName}" CAPITALIZED_BUILD_NAME)
  string(REGEX REPLACE
    "^_"
    ""
    CAPITALIZED_BUILD_NAME_NO_LEADING_UNDERSCORE
    "${CAPITALIZED_BUILD_NAME}"
  )
  set_property(
    GLOBAL
    APPEND
    PROPERTY JFS_AVAILABLE_RUNTIMES
    "${CAPITALIZED_BUILD_NAME_NO_LEADING_UNDERSCORE}"
  )
  # Append to JFS_STATIC_RUNTIME_PATH
  # This path will be relative to the `runtime`
  file(RELATIVE_PATH
    RUNTIME_LIBRARY_PATH
    "${CMAKE_BINARY_DIR}/runtime" # Relative to
    "${buildDir}/libJFSSMTLIBRuntime.a" # FIXME: Not portable
  )
  set_property(
    GLOBAL
    APPEND
    PROPERTY JFS_STATIC_RUNTIME_PATH
    "${RUNTIME_LIBRARY_PATH}"
  )
endmacro()


# TODO: Add more configurations so we can experiment with them from jfs.
AddJFSRuntimeBuild(
  OPTIMIZED
  DEBUG_SYMBOLS
  RUN_UNIT_TESTS
)
AddJFSRuntimeBuild(
  OPTIMIZED
  DEBUG_SYMBOLS
  RUNTIME_ASSERTS
  RUN_UNIT_TESTS
)
# NOTE: There's no config to run with ASan/UBSan but not have runtime
# asserts. It's unlikely we'd want to do that so don't build that
# config for now.
AddJFSRuntimeBuild(
  DEBUG_SYMBOLS
  OPTIMIZED
  RUNTIME_ASSERTS
  ASAN
  UBSAN
  RUN_UNIT_TESTS
)
AddJFSRuntimeBuild(
  DEBUG_SYMBOLS
  OPTIMIZED
  RUNTIME_ASSERTS
  ASAN
  # Don't run tests as covered by config that mixes ASan and UBSan together
)
AddJFSRuntimeBuild(
  DEBUG_SYMBOLS
  OPTIMIZED
  RUNTIME_ASSERTS
  UBSAN
  # Don't run tests as covered by config that mixes ASan and UBSan together
)
