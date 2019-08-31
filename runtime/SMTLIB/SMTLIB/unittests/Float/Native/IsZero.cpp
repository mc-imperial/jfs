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

TEST(IsZero, Float32) {
  ASSERT_FALSE(Float32::getNaN().isZero());
  ASSERT_TRUE(Float32::getPositiveZero().isZero());
  ASSERT_TRUE(Float32::getNegativeZero().isZero());
  ASSERT_FALSE(Float32::getPositiveInfinity().isZero());
  ASSERT_FALSE(Float32::getNegativeInfinity().isZero());
  ASSERT_TRUE(Float32(0.0f).isZero());
  ASSERT_FALSE(Float32(1.0f).isZero());
  Float32 subnormal(BitVector<1>(0x0), BitVector<8>(0x0), BitVector<23>(0x1));
  ASSERT_FALSE(subnormal.isZero());
}

TEST(IsZero, Float64) {
  ASSERT_FALSE(Float64::getNaN().isZero());
  ASSERT_TRUE(Float64::getPositiveZero().isZero());
  ASSERT_TRUE(Float64::getNegativeZero().isZero());
  ASSERT_FALSE(Float64::getPositiveInfinity().isZero());
  ASSERT_FALSE(Float64::getNegativeInfinity().isZero());
  ASSERT_TRUE(Float64(0.0f).isZero());
  ASSERT_FALSE(Float64(1.0f).isZero());
  Float64 subnormal(BitVector<1>(0x0), BitVector<11>(0x0), BitVector<52>(0x1));
  ASSERT_FALSE(subnormal.isZero());
}
