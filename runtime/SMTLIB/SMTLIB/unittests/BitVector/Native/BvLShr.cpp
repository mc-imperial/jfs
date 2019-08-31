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

#define BVLSHR_BRUTE(N)                                                        \
  TEST(bvlshr, BruteForceBv##N) {                                              \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t mask = (UINT64_C(1) << N) - 1;                                \
        uint64_t expected = (y >= N) ? 0 : ((x >> y) & mask);                  \
        EXPECT_EQ(xBv.bvlshr(yBv), expected);                                  \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVLSHR_BRUTE(1);
BVLSHR_BRUTE(2);
BVLSHR_BRUTE(3);
BVLSHR_BRUTE(4);
BVLSHR_BRUTE(5);
BVLSHR_BRUTE(6);
BVLSHR_BRUTE(7);
BVLSHR_BRUTE(8);
BVLSHR_BRUTE(9);
BVLSHR_BRUTE(10);

#define BVLSHR(N, X, Y, E)                                                     \
  TEST(bvlshr, LShr##N##_##X##_##Y) {                                          \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvlshr(y), E);                                                 \
  }
// Bv8
BVLSHR(8, 255, 1, 127)
BVLSHR(8, 255, 2, 63)

// Bv64
BVLSHR(64, 0, 0, 0)
// Simple shifts
BVLSHR(64, 1, 1, 0)
BVLSHR(64, 1, 2, 0)
BVLSHR(64, 1, 3, 0)
BVLSHR(64, 1, 4, 0)

// Overshift
BVLSHR(64, 1, 64, 0)
BVLSHR(64, 1, 65, 0)
