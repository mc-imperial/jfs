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

TEST(Min, Float32) {
  Float32 a = Float32(0.0f);
  Float32 b = Float32(100.0f);
  ASSERT_TRUE(a.min(b) == a);
  ASSERT_TRUE(b.min(a) == a);
  ASSERT_TRUE(a.min(a) == a);
  ASSERT_TRUE(b.min(b) == b);
  Float32 nan = Float32::getNaN();

  // One arg NaN
  ASSERT_TRUE(nan.min(a) == a);
  ASSERT_TRUE(nan.min(a) == a);
  ASSERT_TRUE(a.min(nan) == a);

  // Both NaN
  ASSERT_TRUE(nan.min(nan) == nan);
}

TEST(Min, Float64) {
  Float64 a = Float64(0.0);
  Float64 b = Float64(100.0);
  ASSERT_TRUE(a.min(b) == a);
  ASSERT_TRUE(b.min(a) == a);
  ASSERT_TRUE(a.min(a) == a);
  ASSERT_TRUE(b.min(b) == b);
  Float64 nan = Float64::getNaN();

  // One arg NaN
  ASSERT_TRUE(nan.min(a) == a);
  ASSERT_TRUE(nan.min(a) == a);
  ASSERT_TRUE(a.min(nan) == a);

  // Both NaN
  ASSERT_TRUE(nan.min(nan) == nan);
}
