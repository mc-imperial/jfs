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
#include <math.h>

TEST(IsNegative, Float32) {
  ASSERT_FALSE(Float32::getNaN().isNegative());
  ASSERT_FALSE(Float32::getPositiveZero().isNegative());
  ASSERT_TRUE(Float32::getNegativeZero().isNegative());
  ASSERT_FALSE(Float32::getPositiveInfinity().isNegative());
  ASSERT_TRUE(Float32::getNegativeInfinity().isNegative());
  ASSERT_FALSE(Float32(0.0f).isNegative());
  ASSERT_FALSE(Float32(1.0f).isNegative());
  ASSERT_TRUE(Float32(-1.0f).isNegative());
  Float32 subnormal(BitVector<1>(0x0), BitVector<8>(0x0), BitVector<23>(0x1));
  ASSERT_FALSE(subnormal.isNegative());
  Float32 subnormalNeg(BitVector<1>(0x1), BitVector<8>(0x0),
                       BitVector<23>(0x1));
  ASSERT_TRUE(subnormalNeg.isNegative());
  Float32 negNaN(BitVector<1>(0x1), BitVector<8>(0xff), BitVector<23>(0x1));
  ASSERT_FALSE(negNaN.isNegative());
  Float32 posNaN(BitVector<1>(0x0), BitVector<8>(0xff), BitVector<23>(0x1));
  ASSERT_FALSE(posNaN.isNegative());
}

TEST(IsNegative, Float64) {
  ASSERT_FALSE(Float64::getNaN().isNegative());
  ASSERT_FALSE(Float64::getPositiveZero().isNegative());
  ASSERT_TRUE(Float64::getNegativeZero().isNegative());
  ASSERT_FALSE(Float64::getPositiveInfinity().isNegative());
  ASSERT_TRUE(Float64::getNegativeInfinity().isNegative());
  ASSERT_FALSE(Float64(0.0).isNegative());
  ASSERT_TRUE(Float64(-0.0).isNegative());
  ASSERT_FALSE(Float64(1.0).isNegative());
  ASSERT_TRUE(Float64(-1.0).isNegative());
  Float64 subnormal(BitVector<1>(0x0), BitVector<11>(0x0), BitVector<52>(0x1));
  ASSERT_FALSE(subnormal.isNegative());
  Float64 subnormalNeg(BitVector<1>(0x1), BitVector<11>(0x0),
                       BitVector<52>(0x1));
  ASSERT_TRUE(subnormalNeg.isNegative());
  Float64 negNaN(BitVector<1>(0x1), BitVector<11>(0x7ff), BitVector<52>(0x1));
  ASSERT_FALSE(negNaN.isNegative());
  Float64 posNaN(BitVector<1>(0x0), BitVector<11>(0x7ff), BitVector<52>(0x1));
  ASSERT_FALSE(posNaN.isNegative());
}
