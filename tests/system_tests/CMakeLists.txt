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
# LLVM testing tools
###############################################################################
# FIXME: This is not portable
set(FILECHECK_BIN_PATH "${CMAKE_BINARY_DIR}/bin/FileCheck")

# FIXME: This is not portable
set(NOT_BIN_PATH "${CMAKE_BINARY_DIR}/bin/not")

###############################################################################
# JFS testing tools
###############################################################################
# FIXME: This is not portable
set(YAML_SYNTAX_CHECK_PATH "${CMAKE_BINARY_DIR}/bin/yaml-syntax-check")

###############################################################################
# Configure lit test suite
###############################################################################

# FIXME: This is not portable
set(JFS_TOOL_PATH "${CMAKE_BINARY_DIR}/bin/jfs")
set(JFS_OPT_TOOL_PATH "${CMAKE_BINARY_DIR}/bin/jfs-opt")
set(JFS_SMT_TO_CNF_TOOL_PATH "${CMAKE_BINARY_DIR}/bin/jfs-smt2cnf")
set(JFS_SMT_TO_CXX_TOOL_PATH "${CMAKE_BINARY_DIR}/bin/jfs-smt2cxx")

configure_file(lit.site.cfg.in
  ${CMAKE_CURRENT_BINARY_DIR}/lit.site.cfg
  @ONLY
)

add_custom_target(systemtests
  COMMAND "${LIT_TOOL}" ${LIT_ARGS} "${CMAKE_CURRENT_BINARY_DIR}"
  DEPENDS jfs_tool jfs-opt yaml-syntax-check FileCheck not
  COMMENT "Running system tests"
  ${ADD_CUSTOM_COMMAND_USES_TERMINAL_ARG}
)

# CXXFuzzingBackend customizes the testing harness
add_subdirectory(CXXFuzzingBackend)