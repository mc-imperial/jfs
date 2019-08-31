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

#define BVULT_BRUTE(N)                                                         \
  TEST(bvult, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        bool expected = x < y;                                                 \
        EXPECT_EQ(xBv.bvult(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVULT_BRUTE(1);
BVULT_BRUTE(2);
BVULT_BRUTE(3);
BVULT_BRUTE(4);
BVULT_BRUTE(5);
BVULT_BRUTE(6);
BVULT_BRUTE(7);
BVULT_BRUTE(8);
BVULT_BRUTE(9);
BVULT_BRUTE(10);

#define BVULT(N, X, Y, E)                                                      \
  TEST(bvult, Cmp##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvult(y), E);                                                  \
  }
// Bv64
BVULT(64, 0, 0, false)
BVULT(64, 1, 0, false)
BVULT(64, 0, 1, true)
BVULT(64, 1, 1, false)
