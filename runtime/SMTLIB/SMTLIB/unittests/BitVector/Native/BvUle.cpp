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

#define BVULE_BRUTE(N)                                                         \
  TEST(bvule, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        bool expected = x <= y;                                                \
        EXPECT_EQ(xBv.bvule(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVULE_BRUTE(1);
BVULE_BRUTE(2);
BVULE_BRUTE(3);
BVULE_BRUTE(4);
BVULE_BRUTE(5);
BVULE_BRUTE(6);
BVULE_BRUTE(7);
BVULE_BRUTE(8);
BVULE_BRUTE(9);
BVULE_BRUTE(10);

#define BVULE(N, X, Y, E)                                                      \
  TEST(bvule, Cmp##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvule(y), E);                                                  \
  }
// Bv64
BVULE(64, 0, 0, true)
BVULE(64, 1, 0, false)
BVULE(64, 0, 1, true)
BVULE(64, 1, 1, true)
