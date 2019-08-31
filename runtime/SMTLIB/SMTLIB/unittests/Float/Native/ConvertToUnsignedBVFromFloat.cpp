//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "SMTLIB/Float.h"
#include "gtest/gtest.h"

TEST(ConvertToUnsignedBVFromFloat, zero) {
  ASSERT_EQ(Float32::getPositiveZero().convertToUnsignedBV<32>(JFS_RM_RNE),
            BitVector<32>(0));
  ASSERT_EQ(Float64::getPositiveZero().convertToUnsignedBV<32>(JFS_RM_RNE),
            BitVector<32>(0));
}

TEST(ConvertToUnsignedBVFromFloat, TwoFiveSixPointTwo) {
  ASSERT_EQ(Float32(256.2f).convertToUnsignedBV<32>(JFS_RM_RNE),
            BitVector<32>(256));
  ASSERT_EQ(Float64(256.2).convertToUnsignedBV<32>(JFS_RM_RNE),
            BitVector<32>(256));
}

// FIXME: Write more tests to test the different rounding modes
