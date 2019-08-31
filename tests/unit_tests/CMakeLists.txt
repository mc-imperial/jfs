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
include("${CMAKE_SOURCE_DIR}/cmake/add_jfs_unit_test.cmake")

# Note we assume GTest is already built in `utils/CMakeLists.txt`

# Unit Tests
add_subdirectory(Core)
add_subdirectory(Dummy)
add_subdirectory(FuzzingCommon)

# Set up lit configuration
configure_file(
  "lit-unit-tests-common.site.cfg.in"
  "lit.site.cfg"
  @ONLY
)

get_property(UNIT_TEST_DEPENDS
  GLOBAL
  PROPERTY JFS_UNIT_TEST_TARGETS
)
add_custom_target(jfs_lib_unittests
  COMMAND
    "${CMAKE_COMMAND}" -E env
      "UBSAN_OPTIONS=halt_on_error=1"
      "${LIT_TOOL}" ${LIT_ARGS} "${CMAKE_CURRENT_BINARY_DIR}"
    DEPENDS ${UNIT_TEST_DEPENDS}
    COMMENT "Running JFS library unittests"
    ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)
# Make top level target depend on JFS library unit tests
add_dependencies(unittests jfs_lib_unittests)
