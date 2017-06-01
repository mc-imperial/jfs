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
  Z3Node.cpp
)
target_link_libraries(JFSCore PUBLIC "${Z3_LIBRARIES}")
