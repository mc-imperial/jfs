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
  Native/BvUDiv.cpp
  Native/BvURem.cpp
  Native/BvNeg.cpp
  Native/BvShl.cpp
  Native/BvLShr.cpp
  Native/BvAnd.cpp
  Native/BvOr.cpp
  Native/BvNot.cpp
  Native/BvUle.cpp
  Native/BvUlt.cpp
  Native/BvUgt.cpp
  Native/BvUge.cpp
)
target_link_libraries(BitVector${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntime)
