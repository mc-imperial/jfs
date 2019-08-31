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

TEST(GreaterThanOrEqual, NaNCmpNaN) {
  ASSERT_FALSE(Float32::getNaN().fpgeq(Float32::getNaN()));
  ASSERT_FALSE(Float64::getNaN().fpgeq(Float64::getNaN()));
}

TEST(GreaterThanOrEqual, SameValues) {
  ASSERT_TRUE(Float32(1.0f).fpgeq(1.0f));
  ASSERT_TRUE(Float64(1.0).fpgeq(1.0));
}

TEST(GreaterThanOrEqual, SmallLessBig) {
  ASSERT_FALSE(Float32(1.0f).fpgeq(255.0f));
  ASSERT_FALSE(Float64(1.0).fpgeq(255.0));
}

TEST(GreaterThanOrEqual, BigLessSmall) {
  ASSERT_TRUE(Float32(255.0f).fpgeq(1.0f));
  ASSERT_TRUE(Float64(255.0).fpgeq(1.0));
}
