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

TEST(ConvertToSignedBVFromFloat, positiveZero) {
  ASSERT_EQ(Float32::getPositiveZero().convertToSignedBV<32>(JFS_RM_RNE),
            BitVector<32>(0));
  ASSERT_EQ(Float64::getPositiveZero().convertToSignedBV<32>(JFS_RM_RNE),
            BitVector<32>(0));
}

TEST(ConvertToSignedBVFromFloat, negativeZero) {
  ASSERT_EQ(Float32::getNegativeZero().convertToSignedBV<32>(JFS_RM_RNE),
            BitVector<32>(0));
  ASSERT_EQ(Float64::getNegativeZero().convertToSignedBV<32>(JFS_RM_RNE),
            BitVector<32>(0));
}

TEST(ConvertToSignedBVFromFloat, TwoFiveSixPointTwo) {
  ASSERT_EQ(Float32(256.2f).convertToSignedBV<32>(JFS_RM_RNE),
            BitVector<32>(256));
  ASSERT_EQ(Float64(256.2).convertToSignedBV<32>(JFS_RM_RNE),
            BitVector<32>(256));
}

TEST(ConvertToSignedBVFromFloat, MinusOne) {
  ASSERT_EQ(Float32(-1.0f).convertToSignedBV<8>(JFS_RM_RNE),
            BitVector<8>(0xff));
  ASSERT_EQ(Float64(-1.0f).convertToSignedBV<8>(JFS_RM_RNE),
            BitVector<8>(0xff));
}

// FIXME: Write more tests to test the different rounding modes
