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
include("${CMAKE_SOURCE_DIR}/cmake/add_jfs_unit_test.cmake")

# Build gtest
add_subdirectory(
  "${GTEST_SRC_DIR}"
  "${CMAKE_BINARY_DIR}/utils/googletest"
)

# Unit Tests
add_subdirectory(Dummy)
add_subdirectory(SMTLIBRuntime)


# Set up lit configuration
configure_file(
  "lit-unit-tests-common.site.cfg.in"
  "lit.site.cfg"
  @ONLY
)

# Add a target to run all the unit tests using lit
get_property(UNIT_TEST_DEPENDS
  GLOBAL
  PROPERTY JFS_UNIT_TEST_TARGETS
)
add_custom_target(unittests
  COMMAND
    "${LIT_TOOL}" ${LIT_ARGS} "${CMAKE_CURRENT_BINARY_DIR}"
    DEPENDS ${UNIT_TEST_DEPENDS}
    COMMENT "Running unittests"
    ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)
