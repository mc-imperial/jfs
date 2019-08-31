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

#define BVSHL_BRUTE(N)                                                         \
  TEST(bvshl, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t mask = (UINT64_C(1) << N) - 1;                                \
        uint64_t expected = (y >= N) ? 0 : ((x << y) & mask);                  \
        EXPECT_EQ(xBv.bvshl(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVSHL_BRUTE(1);
BVSHL_BRUTE(2);
BVSHL_BRUTE(3);
BVSHL_BRUTE(4);
BVSHL_BRUTE(5);
BVSHL_BRUTE(6);
BVSHL_BRUTE(7);
BVSHL_BRUTE(8);
BVSHL_BRUTE(9);
BVSHL_BRUTE(10);

#define BVSHL(N, X, Y, E)                                                      \
  TEST(bvshl, Shl##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvshl(y), E);                                                  \
  }

// Bv8
BVSHL(8, 255, 1, 254)
BVSHL(8, 255, 2, 252)

// Bv64
BVSHL(64, 0, 0, 0)
// Simple shifts
BVSHL(64, 1, 1, 2)
BVSHL(64, 1, 2, 4)
BVSHL(64, 1, 3, 8)
BVSHL(64, 1, 4, 16)

// Overshift
BVSHL(64, 1, 64, 0)
BVSHL(64, 1, 65, 0)
