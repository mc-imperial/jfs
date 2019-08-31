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
#include <math.h>

TEST(IsNaN, fromFloat32API) {
  Float32 n = Float32::getNaN();
  ASSERT_TRUE(n.isNaN());
}

TEST(IsNaN, fromFloat64API) {
  Float64 n = Float64::getNaN();
  ASSERT_TRUE(n.isNaN());
}

TEST(IsNaN, onZeroFloat32) {
  Float32 n(0.0f);
  ASSERT_FALSE(n.isNaN());
}

TEST(IsNaN, onZeroFloat64) {
  Float64 n(0.0f);
  ASSERT_FALSE(n.isNaN());
}
