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
add_jfs_unit_test(Logger
  LoggerTests.cpp
)

set(PATH_TO_LOG_FILE "${CMAKE_CURRENT_BINARY_DIR}/test_log.yml")
target_compile_definitions(Logger${UNIT_TEST_EXE_SUFFIX}
  PRIVATE
  "-DPATH_TO_LOG_FILE=${PATH_TO_LOG_FILE}"
)

target_link_libraries(Logger${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntime)
target_link_libraries(Logger${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntimeTestUtil)
