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

#define BVUGT_BRUTE(N)                                                         \
  TEST(bvugt, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        bool expected = x > y;                                                 \
        EXPECT_EQ(xBv.bvugt(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVUGT_BRUTE(1);
BVUGT_BRUTE(2);
BVUGT_BRUTE(3);
BVUGT_BRUTE(4);
BVUGT_BRUTE(5);
BVUGT_BRUTE(6);
BVUGT_BRUTE(7);
BVUGT_BRUTE(8);
BVUGT_BRUTE(9);
BVUGT_BRUTE(10);

#define BVUGT(N, X, Y, E)                                                      \
  TEST(bvugt, Cmp##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvugt(y), E);                                                  \
  }
// Bv64
BVUGT(64, 0, 0, false)
BVUGT(64, 1, 0, true)
BVUGT(64, 0, 1, false)
BVUGT(64, 1, 1, false)
