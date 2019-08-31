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

add_jfs_unit_test(BitVector
  Native/BvAShr.cpp
  Native/BvAlloc.cpp
  Native/BvAdd.cpp
  Native/BvAnd.cpp
  Native/BvComp.cpp
  Native/BvLShr.cpp
  Native/BvMul.cpp
  Native/BvNand.cpp
  Native/BvNeg.cpp
  Native/BvNor.cpp
  Native/BvNot.cpp
  Native/BvOr.cpp
  Native/BvShl.cpp
  Native/BvSub.cpp
  Native/BvUDiv.cpp
  Native/BvSDiv.cpp
  Native/BvSRem.cpp
  Native/BvSMod.cpp
  Native/BvSge.cpp
  Native/BvSgt.cpp
  Native/BvSlt.cpp
  Native/BvSle.cpp
  Native/BvUgt.cpp
  Native/BvUge.cpp
  Native/BvUle.cpp
  Native/BvUlt.cpp
  Native/BvXor.cpp
  Native/BvXNor.cpp
  Native/Concat.cpp
  Native/Equal.cpp
  Native/Extract.cpp
  Native/MakeFromBuffer.cpp
  Native/ZeroExtend.cpp
  Native/SignExtend.cpp
  Native/RotateLeft.cpp
  Native/RotateRight.cpp
  Native/WriteToBuffer.cpp
  NonNative/Concat.cpp
  NonNative/ZeroExtend.cpp
  NonNative/SignExtend.cpp
)
target_link_libraries(BitVector${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntime)
target_link_libraries(BitVector${UNIT_TEST_EXE_SUFFIX} PRIVATE JFSSMTLIBRuntimeTestUtil)
