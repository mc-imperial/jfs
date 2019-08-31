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

// FIXME: We need to use some macro tricks to try all possible
// extraction values.
#define BVEXTRACT_BRUTE(W)                                                     \
  TEST(bvextract, brute##W) {                                                  \
    for (unsigned value = 0; value < ((UINT64_C(1) << W) - 1); ++value) {      \
      BitVector<W> x(value);                                                   \
      auto noOp = x.extract<W>(W - 1, 0);                                      \
      ASSERT_EQ(noOp, value);                                                  \
    }                                                                          \
  }

BVEXTRACT_BRUTE(1)
BVEXTRACT_BRUTE(2)
BVEXTRACT_BRUTE(3)
BVEXTRACT_BRUTE(4)
BVEXTRACT_BRUTE(5)
BVEXTRACT_BRUTE(6)
BVEXTRACT_BRUTE(7)
BVEXTRACT_BRUTE(8)

TEST(bvextract, simple) {
  BitVector<4> x(10);
  auto result = x.extract<2>(3, 2);
  ASSERT_EQ(result, 2);
  auto result2 = x.extract<4>(3, 0);
  ASSERT_EQ(result2, 10);
  auto result3 = x.extract<1>(3, 3);
  ASSERT_EQ(result3, 1);
  auto result4 = x.extract<3>(2, 0);
  ASSERT_EQ(result4, 2);
}
