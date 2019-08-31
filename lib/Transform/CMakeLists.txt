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
jfs_add_component(JFSTransform
  AndHoistingPass.cpp
  BitBlastPass.cpp
  BvBoundPropagationPass.cpp
  ConstantPropagationPass.cpp
  DIMACSOutputPass.cpp
  DuplicateConstraintEliminationPass.cpp
  FpToBvPass.cpp
  QueryPassManager.cpp
  SimpleContradictionsToFalsePass.cpp
  SimplificationPass.cpp
  StandardPasses.cpp
  TrueConstraintEliminationPass.cpp
  Z3QueryPass.cpp
)
target_link_libraries(JFSTransform PUBLIC JFSCore)
