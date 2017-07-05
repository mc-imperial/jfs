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
jfs_add_component(JFSCore
  JFSContext.cpp
  Query.cpp
  SMTLIB2Parser.cpp
  Solver.cpp
  ToolErrorHandler.cpp
  Z3ASTVisitor.cpp
  Z3Node.cpp
)
# Needed for command line support
jfs_get_llvm_components(llvm_components support)

target_link_libraries(JFSCore PUBLIC "${Z3_LIBRARIES}" ${llvm_components})
