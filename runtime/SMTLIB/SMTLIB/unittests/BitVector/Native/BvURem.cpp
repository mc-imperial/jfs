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

#define BVUREM_BRUTE(N)                                                        \
  TEST(bvurem, BruteForceBv##N) {                                              \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t expected = (y == 0) ? (x) : (x % y);                          \
        EXPECT_EQ(xBv.bvurem(yBv), expected);                                  \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVUREM_BRUTE(1);
BVUREM_BRUTE(2);
BVUREM_BRUTE(3);
BVUREM_BRUTE(4);
BVUREM_BRUTE(5);
BVUREM_BRUTE(6);
BVUREM_BRUTE(7);
BVUREM_BRUTE(8);
BVUREM_BRUTE(9);
BVUREM_BRUTE(10);

#define BVUREM(N, X, Y, E)                                                     \
  TEST(bvurem, URem##N##_##X##_##Y) {                                          \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvurem(y), E);                                                 \
  }

// Bv64
BVUREM(64, 0, 0, 0)
// Simple divisor
BVUREM(64, 0, 1, 0)
BVUREM(64, 1, 0, 1)
BVUREM(64, 1, 1, 0)
BVUREM(64, 2, 1, 0)
BVUREM(64, 1, 2, 1)
BVUREM(64, 256, 7, 4)
