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

TEST(ConvertToFloatFromSignedBV, zero) {
  ASSERT_TRUE((Float32::convertFromSignedBV<32>(JFS_RM_RNE, BitVector<32>(0)))
                  .isZero());
  ASSERT_TRUE((Float64::convertFromSignedBV<64>(JFS_RM_RNE, BitVector<64>(0)))
                  .isZero());
}

TEST(ConvertToFloatFromSignedBV, TwoFiveSix) {
  ASSERT_EQ((Float32::convertFromSignedBV<32>(JFS_RM_RNE, BitVector<32>(256))),
            Float32(256.0f));
  ASSERT_EQ((Float64::convertFromSignedBV<32>(JFS_RM_RNE, BitVector<32>(256))),
            Float64(256.0));
}

TEST(ConvertToFloatFromSignedBV, MinusOne) {
  BitVector<8> minusOne(0xff);
  ASSERT_EQ(Float32::convertFromSignedBV<8>(JFS_RM_RNE, minusOne),
            Float32(-1.0f));
  ASSERT_EQ(Float64::convertFromSignedBV<8>(JFS_RM_RNE, minusOne),
            Float64(-1.0));
}

// FIXME: Write more tests to test the different rounding modes
