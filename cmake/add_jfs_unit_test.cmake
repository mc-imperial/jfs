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
if (NOT DEFINED GTEST_SRC_DIR)
  message(FATAL_ERROR "GTEST_SRC_DIR must be defined")
endif()
if (NOT EXISTS "${GTEST_SRC_DIR}")
  message(FATAL_ERROR "GTEST_SRC_DIR (${GTEST_SRC_DIR}) must exist")
endif()

# This keeps track of all the unit test
# targets so we can ensure they are built
# before trying to run them.
define_property(GLOBAL
  PROPERTY JFS_UNIT_TEST_TARGETS
  BRIEF_DOCS "JFS unit tests"
  FULL_DOCS "JFS unit tests"
)

set(GTEST_INCLUDE_DIR "${GTEST_SRC_DIR}/include")

if (NOT IS_DIRECTORY "${GTEST_INCLUDE_DIR}")
  message(FATAL_ERROR
    "Cannot find GTest include directory \"${GTEST_INCLUDE_DIR}\"")
endif()

set (UNIT_TEST_EXE_SUFFIX "Test")
function(add_jfs_unit_test target_name)
  add_executable(${target_name}${UNIT_TEST_EXE_SUFFIX} ${ARGN})
  target_link_libraries(${target_name}${UNIT_TEST_EXE_SUFFIX} PRIVATE jfs_gtest_main)
  target_include_directories(${target_name}${UNIT_TEST_EXE_SUFFIX} BEFORE PRIVATE "${GTEST_INCLUDE_DIR}")
  set_target_properties(${target_name}${UNIT_TEST_EXE_SUFFIX}
    PROPERTIES
    RUNTIME_OUTPUT_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}"
  )
  set_property(GLOBAL
    APPEND
    PROPERTY JFS_UNIT_TEST_TARGETS
    ${target_name}${UNIT_TEST_EXE_SUFFIX}
  )
endfunction()
