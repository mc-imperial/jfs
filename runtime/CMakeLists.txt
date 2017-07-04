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
