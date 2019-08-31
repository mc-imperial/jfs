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
function(jfs_get_external_project_build_command OUTPUT_VAR BUILD_DIR)
  if ("${CMAKE_GENERATOR}" STREQUAL "Unix Makefiles")
    # HACK: This hack means that if the build generator for JFS
    # is Make then `-j` value will passed through to make run
    # to build the external project.
    # See
    # http://cmake.3232098.n2.nabble.com/How-would-I-use-parallel-make-on-ExternalProjects-td5609078.html
    #
    set(JFS_EXTERNAL_PROJECT_BUILD_COMMAND "BUILD_COMMAND" "$(MAKE)")
  else()
    include(ProcessorCount)
    ProcessorCount(NUM_CPUS)
    message(STATUS "Detected ${NUM_CPUS} CPUS. Will run this many jobs when building runtime tests")
    set(JFS_EXTERNAL_PROJECT_BUILD_COMMAND
      "BUILD_COMMAND" "${CMAKE_COMMAND}" "--build" "${BUILD_DIR}" "--" "-j${NUM_CPUS}")
  endif()
  set(${OUTPUT_VAR} ${JFS_EXTERNAL_PROJECT_BUILD_COMMAND} PARENT_SCOPE)
endfunction()
