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
jfs_add_component(JFSTransform
  AndHoistingPass.cpp
  BvBoundPropagationPass.cpp
  ConstantPropagationPass.cpp
  DuplicateConstraintEliminationPass.cpp
  QueryPassManager.cpp
  SimpleContradictionsToFalsePass.cpp
  SimplificationPass.cpp
  StandardPasses.cpp
  TrueConstraintEliminationPass.cpp
  Z3QueryPass.cpp
)
target_link_libraries(JFSTransform PUBLIC JFSCore)
