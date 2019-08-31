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

// FIXME: IEEE-754 2008 (5.5.1 Sign bit operations) says just the sign bit gets
// set to zero so really we should just test that.

TEST(Abs, NaN) {
  ASSERT_TRUE(Float32::getNaN().abs().isNaN());
  ASSERT_TRUE(Float64::getNaN().abs().isNaN());
}

TEST(Abs, NegativeZero) {
  auto absFloat32 = Float32::getNegativeZero().abs();
  ASSERT_TRUE(absFloat32.isPositive());
  ASSERT_TRUE(absFloat32.isZero());
  auto absFloat64 = Float64::getNegativeZero().abs();
  ASSERT_TRUE(absFloat64.isPositive());
  ASSERT_TRUE(absFloat64.isZero());
}

TEST(Abs, PositiveZero) {
  auto absFloat32 = Float32::getPositiveZero().abs();
  ASSERT_TRUE(absFloat32.isPositive());
  ASSERT_TRUE(absFloat32.isZero());
  auto absFloat64 = Float64::getPositiveZero().abs();
  ASSERT_TRUE(absFloat64.isPositive());
  ASSERT_TRUE(absFloat64.isZero());
}

TEST(Abs, NegativeInfinity) {
  auto absFloat32 = Float32::getNegativeInfinity().abs();
  ASSERT_TRUE(absFloat32.isPositive());
  ASSERT_TRUE(absFloat32.isInfinite());
  auto absFloat64 = Float64::getNegativeInfinity().abs();
  ASSERT_TRUE(absFloat64.isPositive());
  ASSERT_TRUE(absFloat64.isInfinite());
}

TEST(Abs, PositiveInfinity) {
  auto absFloat32 = Float32::getPositiveInfinity().abs();
  ASSERT_TRUE(absFloat32.isPositive());
  ASSERT_TRUE(absFloat32.isInfinite());
  auto absFloat64 = Float64::getPositiveInfinity().abs();
  ASSERT_TRUE(absFloat64.isPositive());
  ASSERT_TRUE(absFloat64.isInfinite());
}
