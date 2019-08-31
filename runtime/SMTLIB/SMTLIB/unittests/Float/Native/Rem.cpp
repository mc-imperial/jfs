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

TEST(Rem, NaN) {
  ASSERT_TRUE(Float32::getNaN().rem(Float32(1.0f)).isNaN());
  ASSERT_TRUE(Float64::getNaN().rem(Float64(1.0)).isNaN());
}

TEST(Rem, Simple) {
  ASSERT_EQ(-1.0f, Float32(-7.0f).rem(Float32(3.0f)).getRawData());
  ASSERT_EQ(-1.0, Float64(-7.0f).rem(Float64(3.0f)).getRawData());
}
