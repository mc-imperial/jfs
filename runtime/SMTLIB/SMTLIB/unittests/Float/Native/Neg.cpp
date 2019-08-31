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


TEST(Neg, NaN) {
  auto f32NaN = Float32::getNaN();
  auto f32NaNNegated = f32NaN.neg();
  // msBit32 will only be true if the msb was flipped
  bool msBit32 = ((f32NaN.getRawBits() ^ f32NaNNegated.getRawBits()) >> 31);
  ASSERT_TRUE(msBit32);
  auto f64NaN = Float64::getNaN();
  auto f64NaNNegated = f64NaN.neg();
  // msBit64 will only be true if the msb was flipped
  bool msBit64 = ((f64NaN.getRawBits() ^ f64NaNNegated.getRawBits()) >> 63);
  ASSERT_TRUE(msBit64);
}

TEST(Neg, NegativeZero) {
  auto absFloat32 = Float32::getNegativeZero().neg();
  ASSERT_TRUE(absFloat32.isPositive());
  ASSERT_TRUE(absFloat32.isZero());
  auto absFloat64 = Float64::getNegativeZero().neg();
  ASSERT_TRUE(absFloat64.isPositive());
  ASSERT_TRUE(absFloat64.isZero());
}

TEST(Neg, PositiveZero) {
  auto absFloat32 = Float32::getPositiveZero().neg();
  ASSERT_TRUE(absFloat32.isNegative());
  ASSERT_TRUE(absFloat32.isZero());
  auto absFloat64 = Float64::getPositiveZero().neg();
  ASSERT_TRUE(absFloat64.isNegative());
  ASSERT_TRUE(absFloat64.isZero());
}

TEST(Neg, NegativeInfinity) {
  auto absFloat32 = Float32::getNegativeInfinity().neg();
  ASSERT_TRUE(absFloat32.isPositive());
  ASSERT_TRUE(absFloat32.isInfinite());
  auto absFloat64 = Float64::getNegativeInfinity().neg();
  ASSERT_TRUE(absFloat64.isPositive());
  ASSERT_TRUE(absFloat64.isInfinite());
}

TEST(Neg, PositiveInfinity) {
  auto absFloat32 = Float32::getPositiveInfinity().neg();
  ASSERT_TRUE(absFloat32.isNegative());
  ASSERT_TRUE(absFloat32.isInfinite());
  auto absFloat64 = Float64::getPositiveInfinity().neg();
  ASSERT_TRUE(absFloat64.isNegative());
  ASSERT_TRUE(absFloat64.isInfinite());
}
