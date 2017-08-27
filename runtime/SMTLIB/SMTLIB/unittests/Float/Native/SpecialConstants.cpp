//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "SMTLIB/Float.h"
#include "gtest/gtest.h"
#include <math.h>

TEST(SpecialConstants, PositiveZeroFloat32) {
  Float32 zero = Float32::getPositiveZero();
  ASSERT_EQ(zero.getRawData(), 0.0f);
  ASSERT_FALSE(signbit(zero.getRawData()));
}

TEST(SpecialConstants, PositiveZeroFloat64) {
  Float64 zero = Float64::getPositiveZero();
  ASSERT_EQ(zero.getRawData(), 0.0);
  ASSERT_FALSE(signbit(zero.getRawData()));
}

TEST(SpecialConstants, NegativeZeroFloat32) {
  Float32 zero = Float32::getNegativeZero();
  ASSERT_EQ(zero.getRawData(), 0.0f);
  ASSERT_TRUE(signbit(zero.getRawData()));
}

TEST(SpecialConstants, NegativeZeroFloat64) {
  Float64 zero = Float64::getNegativeZero();
  ASSERT_EQ(zero.getRawData(), 0.0);
  ASSERT_TRUE(signbit(zero.getRawData()));
}

TEST(SpecialConstants, PositiveInfinityFloat32) {
  Float32 infinity = Float32::getPositiveInfinity();
  ASSERT_TRUE(isinf(infinity.getRawData()));
  ASSERT_FALSE(signbit(infinity.getRawData()));
}

TEST(SpecialConstants, PositiveInfinityFloat64) {
  Float64 infinity = Float64::getPositiveInfinity();
  ASSERT_TRUE(isinf(infinity.getRawData()));
  ASSERT_FALSE(signbit(infinity.getRawData()));
}

TEST(SpecialConstants, NegativeInfinityFloat32) {
  Float32 infinity = Float32::getNegativeInfinity();
  ASSERT_TRUE(isinf(infinity.getRawData()));
  ASSERT_TRUE(signbit(infinity.getRawData()));
}

TEST(SpecialConstants, NegativeInfinityFloat64) {
  Float64 infinity = Float64::getNegativeInfinity();
  ASSERT_TRUE(isinf(infinity.getRawData()));
  ASSERT_TRUE(signbit(infinity.getRawData()));
}

TEST(SpecialConstants, NaNFloat32) {
  Float32 num = Float32::getNaN();
  ASSERT_TRUE(isnan(num.getRawData()));
}

TEST(SpecialConstants, NaNFloat64) {
  Float64 num = Float64::getNaN();
  ASSERT_TRUE(isnan(num.getRawData()));
}
