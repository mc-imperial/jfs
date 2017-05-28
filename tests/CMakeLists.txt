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

  # Add global test target
  add_custom_target(check
    COMMENT "Running tests"
  )
if (ENABLE_SYSTEM_TESTS)
  message(STATUS "System tests enabled")
  add_subdirectory(system_tests)
  add_dependencies(check systemtests)
else()
  message(STATUS "System tests disabled")
endif()

if (ENABLE_UNIT_TESTS)
  message(STATUS "Unit tests enabled")
  add_subdirectory(unit_tests)
  add_dependencies(check unittests)
else()
  message(STATUS "Unit tests disabled")
endif()
