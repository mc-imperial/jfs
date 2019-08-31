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

TEST(IsPositive, Float32) {
  ASSERT_FALSE(Float32::getNaN().isPositive());
  ASSERT_TRUE(Float32::getPositiveZero().isPositive());
  ASSERT_FALSE(Float32::getNegativeZero().isPositive());
  ASSERT_TRUE(Float32::getPositiveInfinity().isPositive());
  ASSERT_FALSE(Float32::getNegativeInfinity().isPositive());
  ASSERT_TRUE(Float32(0.0f).isPositive());
  ASSERT_TRUE(Float32(1.0f).isPositive());
  Float32 subnormal(BitVector<1>(0x0), BitVector<8>(0x0), BitVector<23>(0x1));
  ASSERT_TRUE(subnormal.isPositive());
  Float32 subnormalNeg(BitVector<1>(0x1), BitVector<8>(0x0),
                       BitVector<23>(0x1));
  ASSERT_FALSE(subnormalNeg.isPositive());
  Float32 negNaN(BitVector<1>(0x1), BitVector<8>(0xff), BitVector<23>(0x1));
  ASSERT_FALSE(negNaN.isPositive());
  Float32 posNaN(BitVector<1>(0x0), BitVector<8>(0xff), BitVector<23>(0x1));
  ASSERT_FALSE(posNaN.isPositive());
}

TEST(IsPositive, Float64) {
  ASSERT_FALSE(Float64::getNaN().isPositive());
  ASSERT_TRUE(Float64::getPositiveZero().isPositive());
  ASSERT_FALSE(Float64::getNegativeZero().isPositive());
  ASSERT_TRUE(Float64::getPositiveInfinity().isPositive());
  ASSERT_FALSE(Float64::getNegativeInfinity().isPositive());
  ASSERT_TRUE(Float64(0.0).isPositive());
  ASSERT_FALSE(Float64(-0.0).isPositive());
  ASSERT_TRUE(Float64(1.0f).isPositive());
  Float64 subnormal(BitVector<1>(0x0), BitVector<11>(0x0), BitVector<52>(0x1));
  ASSERT_TRUE(subnormal.isPositive());
  Float64 subnormalNeg(BitVector<1>(0x1), BitVector<11>(0x0),
                       BitVector<52>(0x1));
  ASSERT_FALSE(subnormalNeg.isPositive());
  Float64 negNaN(BitVector<1>(0x1), BitVector<11>(0x7ff), BitVector<52>(0x1));
  ASSERT_FALSE(negNaN.isPositive());
  Float64 posNaN(BitVector<1>(0x0), BitVector<11>(0x7ff), BitVector<52>(0x1));
  ASSERT_FALSE(posNaN.isPositive());
}
