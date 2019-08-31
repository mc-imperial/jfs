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

TEST(Max, Float32) {
  Float32 a = Float32(100.0f);
  Float32 b = Float32(0.0f);
  ASSERT_TRUE(a.max(b) == a);
  ASSERT_TRUE(b.max(a) == a);
  ASSERT_TRUE(a.max(a) == a);
  ASSERT_TRUE(b.max(b) == b);
  Float32 nan = Float32::getNaN();

  // One arg NaN
  ASSERT_TRUE(nan.max(a) == a);
  ASSERT_TRUE(nan.max(a) == a);
  ASSERT_TRUE(a.max(nan) == a);

  // Both NaN
  ASSERT_TRUE(nan.max(nan) == nan);
}

TEST(Max, Float64) {
  Float64 a = Float64(100.0);
  Float64 b = Float64(0.0);
  ASSERT_TRUE(a.max(b) == a);
  ASSERT_TRUE(b.max(a) == a);
  ASSERT_TRUE(a.max(a) == a);
  ASSERT_TRUE(b.max(b) == b);
  Float64 nan = Float64::getNaN();

  // One arg NaN
  ASSERT_TRUE(nan.max(a) == a);
  ASSERT_TRUE(nan.max(a) == a);
  ASSERT_TRUE(a.max(nan) == a);

  // Both NaN
  ASSERT_TRUE(nan.max(nan) == nan);
}
