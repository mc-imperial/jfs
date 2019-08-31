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

TEST(LessThanOrEqual, NaNCmpNaN) {
  ASSERT_FALSE(Float32::getNaN().fpleq(Float32::getNaN()));
  ASSERT_FALSE(Float64::getNaN().fpleq(Float64::getNaN()));
}

TEST(LessThanOrEqual, SameValues) {
  ASSERT_TRUE(Float32(1.0f).fpleq(1.0f));
  ASSERT_TRUE(Float64(1.0).fpleq(1.0));
}

TEST(LessThanOrEqual, SmallLessBig) {
  ASSERT_TRUE(Float32(1.0f).fpleq(255.0f));
  ASSERT_TRUE(Float64(1.0).fpleq(255.0));
}

TEST(LessThanOrEqual, BigLessSmall) {
  ASSERT_FALSE(Float32(255.0f).fpleq(1.0f));
  ASSERT_FALSE(Float64(255.0).fpleq(1.0));
}
