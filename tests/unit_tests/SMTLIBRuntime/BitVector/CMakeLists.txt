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

# FIXME: We should be build this with the runtime compiler.
# Not the native compiler
add_jfs_unit_test(BitVector
  Native/BvAlloc.cpp
  Native/BvAdd.cpp
  Native/BvAnd.cpp
  Native/BvLShr.cpp
  Native/BvMul.cpp
  Native/BvNeg.cpp
  Native/BvNot.cpp
  Native/BvOr.cpp
  Native/BvShl.cpp
  Native/BvSub.cpp
  Native/BvUDiv.cpp
  Native/BvURem.cpp
  Native/BvUgt.cpp
  Native/BvUge.cpp
  Native/BvUle.cpp
  Native/BvUlt.cpp
  Native/Concat.cpp
  NonNative/Concat.cpp
)
target_link_libraries(BitVector${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntime)
