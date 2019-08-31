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

TEST(IsSubnormal, Float32) {
  ASSERT_FALSE(Float32::getNaN().isSubnormal());
  ASSERT_FALSE(Float32::getPositiveZero().isSubnormal());
  ASSERT_FALSE(Float32::getNegativeZero().isSubnormal());
  ASSERT_FALSE(Float32::getPositiveInfinity().isSubnormal());
  ASSERT_FALSE(Float32::getNegativeInfinity().isSubnormal());
  ASSERT_FALSE(Float32(0.0f).isSubnormal());
  ASSERT_FALSE(Float32(1.0f).isSubnormal());
  Float32 subnormal(BitVector<1>(0x0), BitVector<8>(0x0), BitVector<23>(0x1));
  ASSERT_TRUE(subnormal.isSubnormal());
}

TEST(IsSubnormal, Float64) {
  ASSERT_FALSE(Float64::getNaN().isSubnormal());
  ASSERT_FALSE(Float64::getPositiveZero().isSubnormal());
  ASSERT_FALSE(Float64::getNegativeZero().isSubnormal());
  ASSERT_FALSE(Float64::getPositiveInfinity().isSubnormal());
  ASSERT_FALSE(Float64::getNegativeInfinity().isSubnormal());
  ASSERT_FALSE(Float64(0.0f).isSubnormal());
  ASSERT_FALSE(Float64(1.0f).isSubnormal());
  Float64 subnormal(BitVector<1>(0x0), BitVector<11>(0x0), BitVector<52>(0x1));
  ASSERT_TRUE(subnormal.isSubnormal());
}
