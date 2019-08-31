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

TEST(LessThan, NaNCmpNaN) {
  ASSERT_FALSE(Float32::getNaN().fplt(Float32::getNaN()));
  ASSERT_FALSE(Float64::getNaN().fplt(Float64::getNaN()));
}

TEST(LessThan, SameValues) {
  ASSERT_FALSE(Float32(1.0f).fplt(1.0f));
  ASSERT_FALSE(Float64(1.0).fplt(1.0));
}

TEST(LessThan, SmallLessBig) {
  ASSERT_TRUE(Float32(1.0f).fplt(255.0f));
  ASSERT_TRUE(Float64(1.0).fplt(255.0));
}

TEST(LessThan, BigLessSmall) {
  ASSERT_FALSE(Float32(255.0f).fplt(1.0f));
  ASSERT_FALSE(Float64(255.0).fplt(1.0));
}
