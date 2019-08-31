#===------------------------------------------------------------------------===#
#
#                                      JFS
#
# Copyright 2017-2018 Daniel Liew
#
# This file is distributed under the MIT license.
# See LICENSE.txt for details.
#
#===------------------------------------------------------------------------===#

###############################################################################
# Minimum CMake version and policies
###############################################################################
cmake_minimum_required(VERSION 2.8.12)
if (POLICY CMP0054)
  # FIXME: This is horrible. With the old behaviour,
  # quoted strings like "MSVC" in if() conditionals
  # get implicitly dereferenced. The NEW behaviour
  # doesn't do this but CMP0054 was only introduced
  # in CMake 3.1 and we support lower versions as the
  # minimum. We could set NEW here but it would be very
  # confusing to use NEW for some builds and OLD for others
  # which could lead to some subtle bugs. Instead when the
  # minimum version is 3.1 change this policy to NEW and remove
  # the hacks in place to work around it.
  cmake_policy(SET CMP0054 OLD)
endif()

if (POLICY CMP0042)
  # Enable `MACOSX_RPATH` by default.
  cmake_policy(SET CMP0042 NEW)
endif()

if (POLICY CMP0037)
  # Disallow reserved target names
  cmake_policy(SET CMP0037 NEW)
endif()

# This overrides the default flags for the different CMAKE_BUILD_TYPEs
set(CMAKE_USER_MAKE_RULES_OVERRIDE_C
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/c_flags_override.cmake")
set(CMAKE_USER_MAKE_RULES_OVERRIDE_CXX
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/cxx_flags_override.cmake")
project(JFS CXX C)

###############################################################################
# Project version
###############################################################################
set(JFS_VERSION_MAJOR 0)
set(JFS_VERSION_MINOR 0)
set(JFS_VERSION_PATCH 0)
set(JFS_VERSION_TWEAK 0)
set(JFS_VERSION "${JFS_VERSION_MAJOR}.${JFS_VERSION_MINOR}.${JFS_VERSION_PATCH}.${JFS_VERSION_TWEAK}")
message(STATUS "JFS version ${JFS_VERSION}")

################################################################################
# Set various useful variables depending on CMake version
################################################################################
if (("${CMAKE_VERSION}" VERSION_EQUAL "3.2") OR ("${CMAKE_VERSION}" VERSION_GREATER "3.2"))
  # In CMake >= 3.2 add_custom_command() supports a ``USES_TERMINAL`` argument
  set(ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG "USES_TERMINAL")
else()
  set(ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG "")
endif()

if (("${CMAKE_VERSION}" VERSION_EQUAL "3.4") OR ("${CMAKE_VERSION}" VERSION_GREATER "3.4"))
  # In CMake >= 3.4 ExternalProject_Add_Step() supports a `USES_TERMINAL` argument
  set(EXTERNAL_PROJECT_ADD_STEP_USES_TERMINAL_ARG "USES_TERMINAL" "1")
else()
  set(EXTERNAL_PROJECT_ADD_STEP_USES_TERMINAL_ARG "")
endif()

################################################################################
# Sanity check - Disallow building in source.
################################################################################
if ("${CMAKE_SOURCE_DIR}" STREQUAL "${CMAKE_BINARY_DIR}")
  message(FATAL_ERROR "In source builds are not allowed. You should invoke "
          "CMake from a different directory.")
endif()

################################################################################
# Build type
################################################################################
message(STATUS "CMake generator: ${CMAKE_GENERATOR}")
if (DEFINED CMAKE_CONFIGURATION_TYPES)
  # Multi-configuration build (e.g. Xcode). Here
  # CMAKE_BUILD_TYPE doesn't matter
  message(STATUS "Available configurations: ${CMAKE_CONFIGURATION_TYPES}")
else()
  # Single configuration generator (e.g. Unix Makefiles, Ninja)
  set(available_build_types Debug Release RelWithDebInfo MinSizeRel)
  if(NOT CMAKE_BUILD_TYPE)
    message(STATUS "CMAKE_BUILD_TYPE is not set. Setting default")
    message(STATUS "The available build types are: ${available_build_types}")
    set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE String
        "Options are ${available_build_types}"
        FORCE)
    # Provide drop down menu options in cmake-gui
    set_property(CACHE CMAKE_BUILD_TYPE PROPERTY STRINGS ${available_build_types})
  endif()
  message(STATUS "Build type: ${CMAKE_BUILD_TYPE}")

  # Check the selected build type is valid
  list(FIND available_build_types "${CMAKE_BUILD_TYPE}" _build_type_index)
  if ("${_build_type_index}" EQUAL "-1")
    message(FATAL_ERROR "\"${CMAKE_BUILD_TYPE}\" is an invalid build type.\n"
      "Use one of the following build types ${available_build_types}")
  endif()
endif()

################################################################################
# Add our CMake module directory to the list of module search directories
################################################################################
list(APPEND CMAKE_MODULE_PATH "${CMAKE_SOURCE_DIR}/cmake/modules")

################################################################################
# Compiler flags for JFS components
# Subsequent commands will append to these. These are used instead of
# directly modifying CMAKE_CXX_FLAGS so that other code can be easily built with
# different flags.
################################################################################
set(JFS_COMPONENT_EXTRA_INCLUDE_DIRS "")
set(JFS_COMPONENT_CXX_DEFINES "")
set(JFS_COMPONENT_CXX_FLAGS "")
set(JFS_SOLVER_LIBRARIES "")
set(JFS_COMPONENT_EXTRA_LIBRARIES "")
include("${CMAKE_SOURCE_DIR}/cmake/jfs_component_add_cxx_flag.cmake")

################################################################################
# JFS include directories
################################################################################
list(APPEND JFS_COMPONENT_EXTRA_INCLUDE_DIRS
  "${CMAKE_BINARY_DIR}/include"
  "${CMAKE_SOURCE_DIR}/include"
)

################################################################################
# Assertions
################################################################################
option(ENABLE_JFS_ASSERTS "Enable JFS assertions" ON)
if (ENABLE_JFS_ASSERTS)
  message(STATUS "JFS assertions enabled")
  # Assume that -DNDEBUG isn't set.
else()
  message(STATUS "JFS assertions disabled")
  list(APPEND JFS_COMPONENT_CXX_DEFINES "NDEBUG")
endif()

################################################################################
# Find LLVM
################################################################################
find_package(LLVM 6.0.0
  CONFIG
)
set(NEEDED_LLVM_VARS
  LLVM_PACKAGE_VERSION
  LLVM_VERSION_MAJOR
  LLVM_VERSION_MINOR
  LLVM_VERSION_PATCH
  LLVM_DEFINITIONS
  LLVM_ENABLE_ASSERTIONS
  LLVM_ENABLE_EH
  LLVM_ENABLE_RTTI
  LLVM_INCLUDE_DIRS
  LLVM_LIBRARY_DIRS
  LLVM_TOOLS_BINARY_DIR
)

foreach (vname ${NEEDED_LLVM_VARS})
  message(STATUS "${vname}: \"${${vname}}\"")
  if (NOT (DEFINED "${vname}"))
    message(FATAL_ERROR "${vname} was not defined")
  endif()
endforeach()
message(STATUS "LLVM_DIR: \"${LLVM_DIR}\"")

# Find Clang
# FIXME: This won't work if LLVM was built with a multi-configuration generator.
set(LLVM_CLANG_CXX_TOOL "${LLVM_TOOLS_BINARY_DIR}/clang++")
if (NOT EXISTS "${LLVM_CLANG_CXX_TOOL}")
  message(FATAL_ERROR "Failed to find clang++ at \"${LLVM_CLANG_CXX_TOOL}\"")
else()
  message(STATUS "Found clang++ at \"${LLVM_CLANG_CXX_TOOL}\"")
endif()

if (LLVM_ENABLE_ASSERTIONS)
  # Certain LLVM debugging macros only work when LLVM was built with asserts
  set(ENABLE_JFS_DEBUG 1) # for config.h
else()
  unset(ENABLE_JFS_DEBUG) # for config.h
endif()

# LLVM_DEFINITIONS aren't lists. Instead they are space separated
string(REPLACE " " ";" LLVM_DEFINITIONS_AS_LIST "${LLVM_DEFINITIONS}")
list(APPEND JFS_COMPONENT_CXX_DEFINES ${LLVM_DEFINITIONS_AS_LIST})

# LLVM_INCLUDE_DIRS aren't lists. Instead they are space separated
string(REPLACE " " ";" LLVM_INCLUDE_DIRS_AS_LIST "${LLVM_INCLUDE_DIRS}")
list(APPEND JFS_COMPONENT_EXTRA_INCLUDE_DIRS ${LLVM_INCLUDE_DIRS_AS_LIST})

if (NOT LLVM_ENABLE_EH)
  if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
    jfs_component_add_cxx_flag("-fno-exceptions" REQUIRED)
  else()
    message(FATAL_ERROR "${CMAKE_CXX_COMPILER_ID} not supported")
  endif()
endif()

if (NOT LLVM_ENABLE_RTTI)
  if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
    jfs_component_add_cxx_flag("-fno-rtti" REQUIRED)
  else()
    message(FATAL_ERROR "${CMAKE_CXX_COMPILER_ID} not supported")
  endif()
endif()
include("${CMAKE_SOURCE_DIR}/cmake/jfs_get_llvm_components.cmake")

################################################################################
# Find Z3
################################################################################
# FIXME: Specify version. Need to upstream support for config setting version.
find_package(Z3 CONFIG)
set(NEEDED_Z3_VARS
  Z3_VERSION_MAJOR
  Z3_VERSION_MINOR
  Z3_VERSION_PATCH
  Z3_VERSION_TWEAK
  Z3_VERSION_STRING
  Z3_C_INCLUDE_DIRS
  Z3_LIBRARIES
)
foreach (vname ${NEEDED_Z3_VARS})
  message(STATUS "${vname}: \"${${vname}}\"")
  if (NOT (DEFINED "${vname}"))
    message(FATAL_ERROR "${vname} was not defined")
  endif()
endforeach()
if ("${Z3_VERSION_STRING}" VERSION_LESS "4.6")
  message(FATAL_ERROR "Need Z3 4.6 or newer")
endif()

list(APPEND JFS_COMPONENT_EXTRA_INCLUDE_DIRS ${Z3_C_INCLUDE_DIRS})

################################################################################
# C++ version
################################################################################
# FIXME: Use CMake's support for this
if (("${CMAKE_CXX_COMPILER_ID}" MATCHES "Clang") OR ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU"))
  set(JFS_USE_CXX_FLAG "-std=c++11")
  jfs_component_add_cxx_flag("${JFS_USE_CXX_FLAG}" REQUIRED)
else()
  set(JFS_USE_CXX_FLAG "")
endif()

################################################################################
# Warnings
################################################################################
include("${CMAKE_SOURCE_DIR}/cmake/compiler_warnings.cmake")

################################################################################
# Report flags
################################################################################
message(STATUS "JFS_COMPONENT_CXX_DEFINES: \"${JFS_COMPONENT_CXX_DEFINES}\"")
message(STATUS "JFS_COMPONENT_EXTRA_INCLUDE_DIRS: \"${JFS_COMPONENT_EXTRA_INCLUDE_DIRS}\"")
message(STATUS "JFS_COMPONENT_CXX_FLAGS: \"${JFS_COMPONENT_CXX_FLAGS}\"")
message(STATUS "JFS_COMPONENT_EXTRA_LIBRARIES: \"${JFS_COMPONENT_EXTRA_LIBRARIES}\"")

################################################################################
# Report default CMake flags
################################################################################
# This is mainly for debugging.
message(STATUS "CMAKE_CXX_FLAGS: \"${CMAKE_CXX_FLAGS}\"")
message(STATUS "CMAKE_EXE_LINKER_FLAGS: \"${CMAKE_EXE_LINKER_FLAGS}\"")
message(STATUS "CMAKE_STATIC_LINKER_FLAGS: \"${CMAKE_STATIC_LINKER_FLAGS}\"")
message(STATUS "CMAKE_SHARED_LINKER_FLAGS: \"${CMAKE_SHARED_LINKER_FLAGS}\"")
if (DEFINED CMAKE_CONFIGURATION_TYPES)
  # Multi configuration generator
  string(TOUPPER "${available_build_types}" build_types_to_report)
else()
  # Single configuration generator
  string(TOUPPER "${CMAKE_BUILD_TYPE}" build_types_to_report)
endif()
foreach (_build_type ${build_types_to_report})
  message(STATUS "CMAKE_CXX_FLAGS_${_build_type}: \"${CMAKE_CXX_FLAGS_${_build_type}}\"")
  message(STATUS "CMAKE_EXE_LINKER_FLAGS_${_build_type}: \"${CMAKE_EXE_LINKER_FLAGS_${_build_type}}\"")
  message(STATUS "CMAKE_SHARED_LINKER_FLAGS_${_build_type}: \"${CMAKE_SHARED_LINKER_FLAGS_${_build_type}}\"")
  message(STATUS "CMAKE_STATIC_LINKER_FLAGS_${_build_type}: \"${CMAKE_STATIC_LINKER_FLAGS_${_build_type}}\"")
endforeach()

################################################################################
# Handle git hash and description
################################################################################
include(${CMAKE_SOURCE_DIR}/cmake/git_utils.cmake)
macro(disable_git_describe)
  message(WARNING "Disabling INCLUDE_GIT_DESCRIBE")
  set(INCLUDE_GIT_DESCRIBE OFF CACHE BOOL "Include git describe output in version output" FORCE)
endmacro()
macro(disable_git_hash)
  message(WARNING "Disabling INCLUDE_GIT_HASH")
  set(INCLUDE_GIT_HASH OFF CACHE BOOL "Include git hash in version output" FORCE)
  unset(Z3GITHASH) # Used in configure_file()
endmacro()
option(INCLUDE_GIT_HASH "Include git hash in version output" ON)
option(INCLUDE_GIT_DESCRIBE "Include git describe output in version output" ON)

set(GIT_DIR "${CMAKE_SOURCE_DIR}/.git")
if (EXISTS "${GIT_DIR}")
  # Try to make CMake configure depend on the current git HEAD so that
  # a re-configure is triggered when the HEAD changes.
  add_git_dir_dependency("${GIT_DIR}" ADD_GIT_DEP_SUCCESS)
  if (ADD_GIT_DEP_SUCCESS)
    if (INCLUDE_GIT_HASH)
      get_git_head_hash("${GIT_DIR}" JFS_GIT_HASH)
      if (NOT JFS_GIT_HASH)
        message(WARNING "Failed to get Git hash")
        disable_git_hash()
      endif()
      message(STATUS "Using Git hash in version output: ${JFS_GIT_HASH}")
    else()
      message(STATUS "Not using Git hash in version output")
      unset(JFS_GIT_HASH) # Used in configure_file()
    endif()
    if (INCLUDE_GIT_DESCRIBE)
      get_git_head_describe("${GIT_DIR}" JFS_GIT_DESCRIPTION)
      if (NOT Z3_GIT_DESCRIPTION)
        message(WARNING "Failed to get Git description")
        disable_git_describe()
      endif()
      message(STATUS "Using Git description in version output: ${JFS_GIT_DESCRIPTION}")
    else()
      message(STATUS "Not including git descrption in version")
    endif()
  else()
    message(WARNING "Failed to add git dependency.")
    disable_git_describe()
    disable_git_hash()
  endif()
else()
  message(STATUS "Failed to find git directory.")
  disable_git_describe()
  disable_git_hash()
endif()

################################################################################
# Generate configuration header files
################################################################################
set(AUTO_GEN_MSG "Automatically generated. DO NOT EDIT")
set(configuration_files "version.h" "depsVersion.h" "config.h")
foreach (configuration_file ${configuration_files})
  configure_file(
    "${CMAKE_SOURCE_DIR}/include/jfs/Config/${configuration_file}.in"
    "${CMAKE_BINARY_DIR}/include/jfs/Config/${configuration_file}"
  )
endforeach()

################################################################################
# Set default location for targets in the build directory
################################################################################
set(CMAKE_ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_LIBRARY_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib)
set(CMAKE_RUNTIME_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/bin)


################################################################################
# Top level unit test target
################################################################################
# This is top level because there are multiple unit test suites to run
add_custom_target(unittests)

################################################################################
# Detect lit tool
################################################################################
# This can't belong in `tests/` because `runtime/` needs to run its own tests.
option(ENABLE_SYSTEM_TESTS "Enable system tests" ON)
option(ENABLE_UNIT_TESTS "Enable unit tests" ON)
if (ENABLE_SYSTEM_TESTS OR ENABLE_UNIT_TESTS)
  # Find lit
  set(LIT_TOOL_NAMES "llvm-lit" "lit")
  find_program(
    LIT_TOOL
    NAMES ${LIT_TOOL_NAMES}
    HINTS "${LLVM_TOOLS_BINARY_DIR}"
    DOC "Path to lit tool"
  )

  set(LIT_ARGS
    "-v;-s"
    CACHE
    STRING
    "Lit arguments"
  )

  if ((NOT LIT_TOOL) OR (NOT EXISTS "${LIT_TOOL}"))
    message(FATAL_ERROR "The lit tool is required for testing.")
  else()
    message(STATUS "Using lit: ${LIT_TOOL}")
  endif()
endif()

################################################################################
# Utilities
################################################################################
set(GTEST_SRC_DIR "${CMAKE_SOURCE_DIR}/utils/googletest/googletest")
add_subdirectory(utils)

################################################################################
# Runtime
################################################################################
add_subdirectory(runtime)
# Sanity checks
if ("${JFS_LLVM_CLANG_CXX_TOOL}" STREQUAL "")
  message(FATAL_ERROR "JFS_LLVM_CLANG_CXX_TOOL not set")
endif()
if (NOT (EXISTS "${JFS_LLVM_CLANG_CXX_TOOL}"))
  message(FATAL_ERROR "JFS_LLVM_CLANG_CXX_TOOL (\"${JFS_LLVM_CLANG_CXX_TOOL}\") doest not exist")
endif()
message(STATUS "JFS_LLVM_CLANG_CXX_TOOL: ${JFS_LLVM_CLANG_CXX_TOOL}")

################################################################################
# Libraries
################################################################################
include("${CMAKE_SOURCE_DIR}/cmake/jfs_add_component.cmake")
add_subdirectory(lib)

################################################################################
# Tools
################################################################################
add_subdirectory(tools)

################################################################################
# Tests
################################################################################
add_subdirectory(tests)
