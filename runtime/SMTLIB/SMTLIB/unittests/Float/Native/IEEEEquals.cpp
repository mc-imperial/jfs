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

namespace {

template <typename T> void checkCommonConstants() {
  ASSERT_TRUE(T::getPositiveZero().ieeeEquals(T::getPositiveZero()));
  ASSERT_TRUE(T::getPositiveZero().ieeeEquals(T::getNegativeZero()));
  ASSERT_TRUE(T::getNegativeZero().ieeeEquals(T::getPositiveZero()));
  ASSERT_TRUE(T::getNegativeZero().ieeeEquals(T::getNegativeZero()));

  ASSERT_TRUE(T::getPositiveInfinity().ieeeEquals(T::getPositiveInfinity()));
  ASSERT_TRUE(T::getNegativeInfinity().ieeeEquals(T::getNegativeInfinity()));

  ASSERT_FALSE(T::getNaN().ieeeEquals(T::getNaN()));
  ASSERT_FALSE(T::getPositiveZero().ieeeEquals(T::getNaN()));
  ASSERT_FALSE(T::getNaN().ieeeEquals(T::getPositiveZero()));

  ASSERT_TRUE(T(1.5).ieeeEquals(T(1.5)));
}
}

TEST(IEEEEquals, DisjointConstantsDisjointFloat32) {
  checkCommonConstants<Float32>();
}

TEST(IEEEEquals, DisjointConstantsDisjointFloat64) {
  checkCommonConstants<Float64>();
}
