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

TEST(IsInfinite, Float32) {
  ASSERT_FALSE(Float32::getNaN().isInfinite());
  ASSERT_FALSE(Float32::getPositiveZero().isInfinite());
  ASSERT_FALSE(Float32::getNegativeZero().isInfinite());
  ASSERT_TRUE(Float32::getPositiveInfinity().isInfinite());
  ASSERT_TRUE(Float32::getNegativeInfinity().isInfinite());
  ASSERT_FALSE(Float32(0.0f).isInfinite());
  ASSERT_FALSE(Float32(1.0f).isInfinite());
  ASSERT_FALSE(Float32(-1.0f).isInfinite());
  Float32 subnormal(BitVector<1>(0x0), BitVector<8>(0x0), BitVector<23>(0x1));
  ASSERT_FALSE(subnormal.isInfinite());
  Float32 subnormalNeg(BitVector<1>(0x1), BitVector<8>(0x0),
                       BitVector<23>(0x1));
  ASSERT_FALSE(subnormalNeg.isInfinite());
  Float32 negNaN(BitVector<1>(0x1), BitVector<8>(0xff), BitVector<23>(0x1));
  ASSERT_FALSE(negNaN.isInfinite());
  Float32 posNaN(BitVector<1>(0x0), BitVector<8>(0xff), BitVector<23>(0x1));
  ASSERT_FALSE(posNaN.isInfinite());
}

TEST(IsInfinite, Float64) {
  ASSERT_FALSE(Float64::getNaN().isInfinite());
  ASSERT_FALSE(Float64::getPositiveZero().isInfinite());
  ASSERT_FALSE(Float64::getNegativeZero().isInfinite());
  ASSERT_TRUE(Float64::getPositiveInfinity().isInfinite());
  ASSERT_TRUE(Float64::getNegativeInfinity().isInfinite());
  ASSERT_FALSE(Float64(0.0).isInfinite());
  ASSERT_FALSE(Float64(-0.0).isInfinite());
  ASSERT_FALSE(Float64(1.0).isInfinite());
  ASSERT_FALSE(Float64(-1.0).isInfinite());
  Float64 subnormal(BitVector<1>(0x0), BitVector<11>(0x0), BitVector<52>(0x1));
  ASSERT_FALSE(subnormal.isInfinite());
  Float64 subnormalNeg(BitVector<1>(0x1), BitVector<11>(0x0),
                       BitVector<52>(0x1));
  ASSERT_FALSE(subnormalNeg.isInfinite());
  Float64 negNaN(BitVector<1>(0x1), BitVector<11>(0x7ff), BitVector<52>(0x1));
  ASSERT_FALSE(negNaN.isInfinite());
  Float64 posNaN(BitVector<1>(0x0), BitVector<11>(0x7ff), BitVector<52>(0x1));
  ASSERT_FALSE(posNaN.isInfinite());
}
