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
#include "SMTLIB/BitVector.h"
#include "gtest/gtest.h"
#include <stdint.h>

TEST(bvalloc, defaultZero8) {
  BitVector<8> x;
  EXPECT_EQ(x, 0);
}

TEST(bvalloc, maxValue8) {
  BitVector<8> x(255);
  EXPECT_EQ(x, 255);
}

TEST(bvalloc, defaultZero64) {
  BitVector<64> x;
  EXPECT_EQ(x, 0);
}

TEST(bvalloc, maxValue64) {
  BitVector<64> x(UINT64_MAX);
  EXPECT_EQ(x, UINT64_MAX);
}
