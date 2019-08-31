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

#define BVAND_BRUTE(N)                                                         \
  TEST(bvand, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t expected = (x & y);                                           \
        EXPECT_EQ(xBv.bvand(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVAND_BRUTE(1);
BVAND_BRUTE(2);
BVAND_BRUTE(3);
BVAND_BRUTE(4);
BVAND_BRUTE(5);
BVAND_BRUTE(6);
BVAND_BRUTE(7);
BVAND_BRUTE(8);
BVAND_BRUTE(9);
BVAND_BRUTE(10);

#define BVAND(N, X, Y, E)                                                      \
  TEST(bvand, And##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvand(y), E);                                                  \
  }
// Bv64
BVAND(64, 0, 0, 0)
// Simple and
BVAND(64, 8, 9, 8)
