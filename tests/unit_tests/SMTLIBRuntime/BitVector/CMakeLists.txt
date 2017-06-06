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
add_jfs_unit_test(BitVector
  Native/BvAlloc.cpp
  Native/BvAdd.cpp
  Native/BvSub.cpp
  Native/BvMul.cpp
)
target_link_libraries(BitVector${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntime)
