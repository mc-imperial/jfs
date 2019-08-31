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
