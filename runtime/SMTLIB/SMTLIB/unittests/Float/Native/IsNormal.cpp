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

TEST(IsNormal, Float32) {
  ASSERT_FALSE(Float32::getNaN().isNormal());
  ASSERT_FALSE(Float32::getPositiveZero().isNormal());
  ASSERT_FALSE(Float32::getNegativeZero().isNormal());
  ASSERT_FALSE(Float32::getPositiveInfinity().isNormal());
  ASSERT_FALSE(Float32::getNegativeInfinity().isNormal());
  ASSERT_FALSE(Float32(0.0f).isNormal());
  ASSERT_TRUE(Float32(1.0f).isNormal());
  Float32 subnormal(BitVector<1>(0x0), BitVector<8>(0x0), BitVector<23>(0x1));
  ASSERT_FALSE(subnormal.isNormal());
}

TEST(IsNormal, Float64) {
  ASSERT_FALSE(Float64::getNaN().isNormal());
  ASSERT_FALSE(Float64::getPositiveZero().isNormal());
  ASSERT_FALSE(Float64::getNegativeZero().isNormal());
  ASSERT_FALSE(Float64::getPositiveInfinity().isNormal());
  ASSERT_FALSE(Float64::getNegativeInfinity().isNormal());
  ASSERT_FALSE(Float64(0.0f).isNormal());
  ASSERT_TRUE(Float64(1.0f).isNormal());
  Float64 subnormal(BitVector<1>(0x0), BitVector<11>(0x0), BitVector<52>(0x1));
  ASSERT_FALSE(subnormal.isNormal());
}
