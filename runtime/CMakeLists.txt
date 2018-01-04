#===------------------------------------------------------------------------===#
#
#                         JFS - The JIT Fuzzing Solver
#
# Copyright 2017-2018 Daniel Liew
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#

###############################################################################
# Runtime copy of Clang++ and dependent libraries
###############################################################################
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/bin")
# `clang++` might be a symlink so resolve to real path
get_filename_component(LLVM_CLANG_CXX_TOOL_REAL_PATH
  "${LLVM_CLANG_CXX_TOOL}" REALPATH
)
get_filename_component(LLVM_CLANG_CXX_TOOL_NAME
  "${LLVM_CLANG_CXX_TOOL}"
  NAME
)
# FIXME: Creating symlinks won't work on Windows
set(JFS_LLVM_CLANG_CXX_TOOL
  "${CMAKE_CURRENT_BINARY_DIR}/bin/${LLVM_CLANG_CXX_TOOL_NAME}"
)
execute_process(COMMAND
  "${CMAKE_COMMAND}" -E create_symlink "${LLVM_CLANG_CXX_TOOL_REAL_PATH}"
  "${JFS_LLVM_CLANG_CXX_TOOL}"
)
# Handle Clang runtime
file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/lib")
get_filename_component(LLVM_BIN_DIR
  "${LLVM_CLANG_CXX_TOOL_REAL_PATH}"
  DIRECTORY
)
get_filename_component(LLVM_ROOT_DIR
  "${LLVM_BIN_DIR}"
  DIRECTORY
)
set(CLANG_RUNTIME_DIR "${LLVM_ROOT_DIR}/lib/clang")
if (NOT (EXISTS "${CLANG_RUNTIME_DIR}"))
  message(FATAL_ERROR
    "Cannot find Clang runtime directory \"${CLANG_RUNTIME_DIR}\""
  )
endif()
# FIXME: Creating symlinks won't work on Windows
execute_process(COMMAND
  "${CMAKE_COMMAND}" -E create_symlink "${CLANG_RUNTIME_DIR}"
  "${CMAKE_CURRENT_BINARY_DIR}/lib/clang"
)
# Make availble to main `CMakeLists.txt` so we can use this elsewhere.
set(JFS_LLVM_CLANG_CXX_TOOL "${JFS_LLVM_CLANG_CXX_TOOL}" PARENT_SCOPE)

###############################################################################
# Build LibFuzzer
###############################################################################
# We build LibFuzzer as an external project using Clang. We
# build it in different configurations.
include(ExternalProject)
include(${CMAKE_SOURCE_DIR}/cmake/jfs_external_project_utils.cmake)

# TODO: Add more
set(LibFuzzerBuildTypes RelWithDebInfo)

foreach (buildType ${LibFuzzerBuildTypes})
  set(buildDir "${CMAKE_CURRENT_BINARY_DIR}/LibFuzzer_${buildType}")
  jfs_get_external_project_build_command(JFS_EXTERNAL_PROJECT_BUILD_COMMAND ${buildDir})
  ExternalProject_Add(BuildLibFuzzerRuntime_${buildType}
    SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/LibFuzzer"
    # FIXME: We should allow other generators
    CMAKE_GENERATOR "Unix Makefiles"
    CMAKE_ARGS
      "-DCMAKE_CXX_COMPILER=${LLVM_CLANG_CXX_TOOL}"
      "-DCMAKE_BUILD_TYPE=${buildType}"
    BINARY_DIR "${buildDir}"
    BUILD_ALWAYS 1
    ${JFS_EXTERNAL_PROJECT_BUILD_COMMAND}
    # Don't run install command
    INSTALL_COMMAND ""
    # FIXME: Guard these based on CMake version
    USES_TERMINAL_BUILD 1
    USES_TERMINAL_CONFIGURE 1
  )
endforeach()

###############################################################################
# SMTLIB runtime
###############################################################################
add_subdirectory(SMTLIB)
