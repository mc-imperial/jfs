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
# Utility library
###############################################################################
add_library(JFSSMTLIBRuntimeTestUtil
  SMTLIBRuntimeTestUtil.cpp
)
target_include_directories(JFSSMTLIBRuntimeTestUtil
  PUBLIC ${CMAKE_CURRENT_SOURCE_DIR}
)

###############################################################################
# Import GTest targets
###############################################################################
# FIXME:
# This assumes that the runtime compiler and host compiler are ABI compatible.
# You would hope that they are but maybe we should build GTest again with the
# runtime compiler?
if (NOT EXISTS "${JFS_GTEST_EXPORT_FILE}")
  message(FATAL_ERROR "Cannot find JFS_GTEST_EXPORT_FILE: \"${JFS_GTEST_EXPORT_FILE}\"")
endif()
include("${JFS_GTEST_EXPORT_FILE}")

###############################################################################
# Declare unit tests
###############################################################################
include("${JFS_SOURCE_ROOT}/cmake/add_jfs_unit_test.cmake")
add_subdirectory(BitVector)
add_subdirectory(Core)
add_subdirectory(Float)
add_subdirectory(Logger)

###############################################################################
# Setup targets for running unittests with lit
###############################################################################
# Set up lit configuration
# Set test suite name
set(UNIT_TEST_SUITE_NAME "JFS ")
if (USE_ASAN)
  string(APPEND UNIT_TEST_SUITE_NAME "ASan ")
endif()
if (USE_ASAN)
  string(APPEND UNIT_TEST_SUITE_NAME "UBSan ")
endif()
string(APPEND UNIT_TEST_SUITE_NAME "${CMAKE_BUILD_TYPE} Runtime unit tests")
configure_file(
  "lit-unit-tests-common.site.cfg.in"
  "lit.site.cfg"
  @ONLY
)

if (NOT EXISTS "${LIT_TOOL}")
  message(FATAL_ERROR "LIT_TOOL \"${LIT_TOOL}\" does not exist")
endif()

get_property(UNIT_TEST_DEPENDS
  GLOBAL
  PROPERTY JFS_UNIT_TEST_TARGETS
)
add_custom_target(jfs_runtime_unittests
  COMMAND
    "${CMAKE_COMMAND}" -E env
      "UBSAN_OPTIONS=halt_on_error=1"
      "${LIT_TOOL}" ${LIT_ARGS} "${CMAKE_CURRENT_BINARY_DIR}"
    DEPENDS ${UNIT_TEST_DEPENDS}
    ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)
