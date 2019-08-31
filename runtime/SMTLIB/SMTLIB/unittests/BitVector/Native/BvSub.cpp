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

#define BVSUB_BRUTE(N)                                                         \
  TEST(bvsub, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t expected = (x - y) % (1 << N);                                \
        EXPECT_EQ(xBv.bvsub(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVSUB_BRUTE(1);
BVSUB_BRUTE(2);
BVSUB_BRUTE(3);
BVSUB_BRUTE(4);
BVSUB_BRUTE(5);
BVSUB_BRUTE(6);
BVSUB_BRUTE(7);
BVSUB_BRUTE(8);
BVSUB_BRUTE(9);
BVSUB_BRUTE(10);

#define BVSUB(N, X, Y, E)                                                      \
  TEST(bvsub, Sub##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvsub(y), E);                                                  \
  }
// Bv64
BVSUB(64, 0, 0, 0)
// Simple subtraction
BVSUB(64, 1, 0, 1)
// Underflow
BVSUB(64, 0, 1, UINT64_MAX)
BVSUB(64, 0, 2, UINT64_MAX - 1)
BVSUB(64, 0, 3, UINT64_MAX - 2)
