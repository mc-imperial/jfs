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

################################################################################
# Generate SMTLIBRuntimes.h
################################################################################
get_property(
  JFS_AVAILABLE_RUNTIMES
  GLOBAL
  PROPERTY JFS_AVAILABLE_RUNTIMES
)
get_property(
  JFS_STATIC_RUNTIME_PATH
  GLOBAL
  PROPERTY JFS_STATIC_RUNTIME_PATH
)
set(SMTLIB_RUNTIME_ENUM_ENTRIES "")
foreach (runtime ${JFS_AVAILABLE_RUNTIMES})
  string(APPEND SMTLIB_RUNTIME_ENUM_ENTRIES "  ${runtime},\n")
endforeach()
configure_file(
  "SMTLIBRuntimes.h.in"
  "${CMAKE_BINARY_DIR}/include/jfs/FuzzingCommon/SMTLIBRuntimes.h"
  @ONLY
)
unset(SMTLIB_RUNTIME_ENUM_ENTRIES)
################################################################################
# Generate SMTLIBRuntimes.cpp
################################################################################
set(getSMTLIBRuntimeAsCStringEntries "")
set(getSMTLIBRuntimePathEntries "")
list(LENGTH JFS_AVAILABLE_RUNTIMES JFS_AVAILABLE_RUNTIMES_LENGTH)
list(LENGTH JFS_STATIC_RUNTIME_PATH JFS_STATIC_RUNTIME_PATH_LENGTH)
if (NOT ("${JFS_AVAILABLE_RUNTIMES_LENGTH}" EQUAL "${JFS_STATIC_RUNTIME_PATH_LENGTH}"))
  message(FATAL_ERROR "Length mismatch")
endif()
set(index 0)
while ("${index}" LESS "${JFS_AVAILABLE_RUNTIMES_LENGTH}")
  list(GET JFS_AVAILABLE_RUNTIMES ${index} runtime_enum)
  list(GET JFS_STATIC_RUNTIME_PATH ${index} runtime_path)

  string(APPEND getSMTLIBRuntimeAsCStringEntries
    "  case SMTLIBRuntimeTy::${runtime_enum}:\n    return \"${runtime_enum}\";\n"
  )
  string(APPEND getSMTLIBRuntimePathEntries
    "  case SMTLIBRuntimeTy::${runtime_enum}:\n    return \"${runtime_path}\";\n"
  )
  math(EXPR index "${index}+1")
endwhile()
configure_file(
  "SMTLIBRuntimes.cpp.in"
  "${CMAKE_CURRENT_BINARY_DIR}/SMTLIBRuntimes.cpp"
  @ONLY
)
message(STATUS "JFS_AVAILABLE_RUNTIMES: ${JFS_AVAILABLE_RUNTIMES}")
message(STATUS "JFS_STATIC_RUNTIME_PATH: ${JFS_STATIC_RUNTIME_PATH}")

################################################################################
# JFSFuzzingCommon component
################################################################################

jfs_add_component(JFSFuzzingCommon
  BufferAssignment.cpp
  BufferElement.cpp
  CommandLineCategory.cpp
  DummyFuzzingSolver.cpp
  EqualityExtractionPass.cpp
  FileSerializableModel.cpp
  FreeVariableToBufferAssignmentPass.cpp
  FreeVariableToBufferAssignmentPassOptions.cpp
  FuzzingSolver.cpp
  FuzzingSolverOptions.cpp
  FuzzingAnalysisInfo.cpp
  JFSRuntimeFuzzingStat.cpp
  LibFuzzerInvocationManager.cpp
  LibFuzzerOptions.cpp
  "${CMAKE_CURRENT_BINARY_DIR}/SMTLIBRuntimes.cpp"
  SeedGenerator.cpp
  SeedManager.cpp
  SeedManagerStat.cpp
  SortConformanceCheckPass.cpp
  WorkingDirectoryManager.cpp
  # FIXME: This is a hack. Can we do this in a cleaner way?
  # Runtime code
  ${CMAKE_SOURCE_DIR}/runtime/SMTLIB/SMTLIB/NativeBitVector.cpp
)

# JFSFuzzingCommon needs to build some of the runtime functions
# into itself so add the include the head path
target_include_directories(JFSFuzzingCommon
  PRIVATE
  "${CMAKE_SOURCE_DIR}/runtime/SMTLIB"
)
# HACK: Make runtime asserts into aborts so that when we use runtime
# functions directly we always use its asserts.
target_compile_definitions(JFSFuzzingCommon
  PRIVATE
  JFS_RUNTIME_FAILURE_CALLS_ABORT
  ENABLE_JFS_RUNTIME_ASSERTS
)


target_link_libraries(JFSFuzzingCommon
  PUBLIC
  JFSTransform
  JFSCore
  JFSSupport
)

add_subdirectory(CmdLine)
