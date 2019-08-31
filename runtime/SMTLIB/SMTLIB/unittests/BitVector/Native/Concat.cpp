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

#define BVCONCAT_BRUTE(XW, YW)                                                 \
  TEST(bvconcat, concat_##XW##_##YW) {                                         \
    for (unsigned xvalue = 0; xvalue < (UINT64_C(1) << XW) - 1; ++xvalue) {    \
      for (unsigned yvalue = 0; yvalue < (UINT64_C(1) << YW) - 1; ++yvalue) {  \
        BitVector<XW> x(xvalue);                                               \
        BitVector<YW> y(yvalue);                                               \
        EXPECT_EQ(x, xvalue);                                                  \
        EXPECT_EQ(y, yvalue);                                                  \
        BitVector<XW + YW> result = x.concat(y);                               \
        uint64_t expected = (xvalue << YW) | yvalue;                           \
        EXPECT_EQ(result, expected);                                           \
      }                                                                        \
    }                                                                          \
  }

// FIXME: Express this in a more compact way
// Brute force the combinations
BVCONCAT_BRUTE(1, 2)
BVCONCAT_BRUTE(1, 3)
BVCONCAT_BRUTE(1, 4)
BVCONCAT_BRUTE(1, 5)
BVCONCAT_BRUTE(1, 6)
BVCONCAT_BRUTE(1, 7)
BVCONCAT_BRUTE(1, 8)
BVCONCAT_BRUTE(2, 1)
BVCONCAT_BRUTE(2, 2)
BVCONCAT_BRUTE(2, 3)
BVCONCAT_BRUTE(2, 4)
BVCONCAT_BRUTE(2, 5)
BVCONCAT_BRUTE(2, 6)
BVCONCAT_BRUTE(2, 7)
BVCONCAT_BRUTE(2, 8)
BVCONCAT_BRUTE(3, 1)
BVCONCAT_BRUTE(3, 2)
BVCONCAT_BRUTE(3, 3)
BVCONCAT_BRUTE(3, 4)
BVCONCAT_BRUTE(3, 5)
BVCONCAT_BRUTE(3, 6)
BVCONCAT_BRUTE(3, 7)
BVCONCAT_BRUTE(3, 8)
BVCONCAT_BRUTE(4, 1)
BVCONCAT_BRUTE(4, 2)
BVCONCAT_BRUTE(4, 3)
BVCONCAT_BRUTE(4, 4)
BVCONCAT_BRUTE(4, 5)
BVCONCAT_BRUTE(4, 6)
BVCONCAT_BRUTE(4, 7)
BVCONCAT_BRUTE(4, 8)
BVCONCAT_BRUTE(5, 1)
BVCONCAT_BRUTE(5, 2)
BVCONCAT_BRUTE(5, 3)
BVCONCAT_BRUTE(5, 4)
BVCONCAT_BRUTE(5, 5)
BVCONCAT_BRUTE(5, 6)
BVCONCAT_BRUTE(5, 7)
BVCONCAT_BRUTE(5, 8)
BVCONCAT_BRUTE(6, 1)
BVCONCAT_BRUTE(6, 2)
BVCONCAT_BRUTE(6, 3)
BVCONCAT_BRUTE(6, 4)
BVCONCAT_BRUTE(6, 5)
BVCONCAT_BRUTE(6, 6)
BVCONCAT_BRUTE(6, 7)
BVCONCAT_BRUTE(6, 8)
BVCONCAT_BRUTE(7, 1)
BVCONCAT_BRUTE(7, 2)
BVCONCAT_BRUTE(7, 3)
BVCONCAT_BRUTE(7, 4)
BVCONCAT_BRUTE(7, 5)
BVCONCAT_BRUTE(7, 6)
BVCONCAT_BRUTE(7, 7)
BVCONCAT_BRUTE(7, 8)
BVCONCAT_BRUTE(8, 1)
BVCONCAT_BRUTE(8, 2)
BVCONCAT_BRUTE(8, 3)
BVCONCAT_BRUTE(8, 4)
BVCONCAT_BRUTE(8, 5)
BVCONCAT_BRUTE(8, 6)
BVCONCAT_BRUTE(8, 7)
BVCONCAT_BRUTE(8, 8)
