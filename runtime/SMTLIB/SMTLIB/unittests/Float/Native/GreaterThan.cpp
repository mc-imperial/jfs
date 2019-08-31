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

TEST(GreaterThan, NaNCmpNaN) {
  ASSERT_FALSE(Float32::getNaN().fpgt(Float32::getNaN()));
  ASSERT_FALSE(Float64::getNaN().fpgt(Float64::getNaN()));
}

TEST(GreaterThan, SameValues) {
  ASSERT_FALSE(Float32(1.0f).fpgt(1.0f));
  ASSERT_FALSE(Float64(1.0).fpgt(1.0));
}

TEST(GreaterThan, SmallLessBig) {
  ASSERT_FALSE(Float32(1.0f).fpgt(255.0f));
  ASSERT_FALSE(Float64(1.0).fpgt(255.0));
}

TEST(GreaterThan, BigLessSmall) {
  ASSERT_TRUE(Float32(255.0f).fpgt(1.0f));
  ASSERT_TRUE(Float64(255.0).fpgt(1.0));
}
