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
jfs_add_component(JFSSupport
  CancellableProcess.cpp
  ErrorMessages.cpp
  FileUtils.cpp
  JFSStat.cpp
  ScopedTimer.cpp
  StatisticsManager.cpp
  Timer.cpp
  version.cpp
)

# Needed for command line support
jfs_get_llvm_components(llvm_components support)

target_link_libraries(JFSSupport PUBLIC ${llvm_components})
