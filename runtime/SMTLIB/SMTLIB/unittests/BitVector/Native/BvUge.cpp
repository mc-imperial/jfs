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

#define BVUGE_BRUTE(N)                                                         \
  TEST(bvuge, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        bool expected = x >= y;                                                \
        EXPECT_EQ(xBv.bvuge(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVUGE_BRUTE(1);
BVUGE_BRUTE(2);
BVUGE_BRUTE(3);
BVUGE_BRUTE(4);
BVUGE_BRUTE(5);
BVUGE_BRUTE(6);
BVUGE_BRUTE(7);
BVUGE_BRUTE(8);
BVUGE_BRUTE(9);
BVUGE_BRUTE(10);

#define BVUGE(N, X, Y, E)                                                      \
  TEST(bvuge, Cmp##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvuge(y), E);                                                  \
  }
// Bv64
BVUGE(64, 0, 0, true)
BVUGE(64, 1, 0, true)
BVUGE(64, 0, 1, false)
BVUGE(64, 1, 1, true)
