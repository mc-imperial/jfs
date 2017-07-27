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
set(RUNTIME_HEADERS "BitVector.h" "BufferRef.h" "Core.h" "jassert.h")
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

# Build two copies of the runtime one for use in JFS and one for
# ASan+UBSan testing
include(ExternalProject)
include(${CMAKE_SOURCE_DIR}/cmake/jfs_external_project_utils.cmake)
# TODO: May want more configurations in the future.
macro(AddJFSRuntimeBuild buildName buildType)
  set(buildDir "${CMAKE_CURRENT_BINARY_DIR}/SMTLIB_${buildName}")
  jfs_get_external_project_build_command(JFS_EXTERNAL_PROJECT_BUILD_COMMAND ${buildDir})
  ExternalProject_Add(BuildSMTLIBRuntime_${buildName}
    DEPENDS jfs_gtest_main jfs_gtest
    SOURCE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/SMTLIB"
    # FIXME: We should allow other generators
    CMAKE_GENERATOR "Unix Makefiles"
    CMAKE_ARGS
      "-DCMAKE_CXX_COMPILER=${LLVM_CLANG_CXX_TOOL}"
      "-DCMAKE_BUILD_TYPE=${buildType}"
      "-DJFS_BINARY_ROOT=${CMAKE_BINARY_DIR}"
      "-DJFS_SOURCE_ROOT=${CMAKE_SOURCE_DIR}"
      "-DJFS_GTEST_EXPORT_FILE=${JFS_GTEST_EXPORT_FILE}"
      "-DGTEST_SRC_DIR=${GTEST_SRC_DIR}"
      "-DLIT_TOOL:string=${LIT_TOOL}"
      ${ARGN} # Additional CMake arguments
    CMAKE_CACHE_ARGS
      # HACK: We have to pass `LIT_ARGS` this way because
      # its a list and passing it in `CMAKE_ARGS` doesn't
      # seem to work.
      "-DLIT_ARGS:string=${LIT_ARGS}"
    BINARY_DIR "${buildDir}"
    BUILD_ALWAYS 1
    ${JFS_EXTERNAL_PROJECT_BUILD_COMMAND}
    # Don't run install command
    INSTALL_COMMAND ""
    # FIXME: Guard these based on CMake version
    USES_TERMINAL_BUILD 1
    USES_TERMINAL_CONFIGURE 1
  )
# Add custom target that invokes the unit teset target inside the external project
add_custom_target(jfs_runtime_${buildName}_unittests
  COMMENT "Runing JFS ${buildName} Runtime unittests"
  COMMAND
  "${CMAKE_COMMAND}" --build "${buildDir}/unittests" --target jfs_runtime_unittests
  DEPENDS BuildSMTLIBRuntime_${buildName}
  USES_TERMINAL
)
add_dependencies(unittests jfs_runtime_${buildName}_unittests)
endmacro()

# TODO: Automatically generate a header and source file that JFS can
# consume so it knows about each of the runtime configurations.

# TODO: Add more configurations so we can experiment with them from jfs.

# TODO: Can we speed up linking by not emitting debug symbols?
AddJFSRuntimeBuild(Optimized_DbgSym RelWithDebInfo
  -DENABLE_JFS_RUNTIME_ASSERTS=OFF
)
AddJFSRuntimeBuild(Optimized_DbgSym_ASan_UBSan_RuntimeAsserts
  RelWithDebInfo
  -DUSE_ASAN=ON
  -DUSE_UBSAN=ON
  -DENABLE_JFS_RUNTIME_ASSERTS=ON
)
