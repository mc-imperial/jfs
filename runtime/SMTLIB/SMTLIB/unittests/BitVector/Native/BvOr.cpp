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

#define BVOR_BRUTE(N)                                                          \
  TEST(bvor, BruteForceBv##N) {                                                \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t expected = (x | y);                                           \
        EXPECT_EQ(xBv.bvor(yBv), expected);                                    \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVOR_BRUTE(1);
BVOR_BRUTE(2);
BVOR_BRUTE(3);
BVOR_BRUTE(4);
BVOR_BRUTE(5);
BVOR_BRUTE(6);
BVOR_BRUTE(7);
BVOR_BRUTE(8);
BVOR_BRUTE(9);
BVOR_BRUTE(10);

#define BVOR(N, X, Y, E)                                                       \
  TEST(bvor, Or##N##_##X##_##Y) {                                              \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvor(y), E);                                                   \
  }
// Bv64
BVOR(64, 0, 0, 0)
// Simple and
BVOR(64, 8, 9, 9)
