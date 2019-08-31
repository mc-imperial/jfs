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

#define BVUDIV_BRUTE(N)                                                        \
  TEST(bvudiv, BruteForceBv##N) {                                              \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t expected = (y == 0) ? ((1 << N) - 1) : (x / y);               \
        EXPECT_EQ(xBv.bvudiv(yBv), expected);                                  \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVUDIV_BRUTE(1);
BVUDIV_BRUTE(2);
BVUDIV_BRUTE(3);
BVUDIV_BRUTE(4);
BVUDIV_BRUTE(5);
BVUDIV_BRUTE(6);
BVUDIV_BRUTE(7);
BVUDIV_BRUTE(8);
BVUDIV_BRUTE(9);
BVUDIV_BRUTE(10);

#define BVUDIV(N, X, Y, E)                                                     \
  TEST(bvudiv, UDiv##N##_##X##_##Y) {                                          \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvudiv(y), E);                                                 \
  }
// Bv64
BVUDIV(64, 0, 0, UINT64_MAX)
// Simple divisor
BVUDIV(64, 0, 1, 0)
BVUDIV(64, 1, 0, UINT64_MAX)
BVUDIV(64, 1, 1, 1)
BVUDIV(64, 2, 1, 2)
BVUDIV(64, 1, 2, 0)
BVUDIV(64, 256, 7, 36)
