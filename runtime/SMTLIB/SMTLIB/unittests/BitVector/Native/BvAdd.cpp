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

#define BVADD_BRUTE(N)                                                         \
  TEST(bvadd, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t expected = (x + y) % (1 << N);                                \
        EXPECT_EQ(xBv.bvadd(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVADD_BRUTE(1);
BVADD_BRUTE(2);
BVADD_BRUTE(3);
BVADD_BRUTE(4);
BVADD_BRUTE(5);
BVADD_BRUTE(6);
BVADD_BRUTE(7);
BVADD_BRUTE(8);
BVADD_BRUTE(9);
BVADD_BRUTE(10);

#define BVADD(N, X, Y, E)                                                      \
  TEST(bvadd, Add##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvadd(y), E);                                                  \
  }

// Bv64
BVADD(64, 0, 0, 0)
// Simple addition
BVADD(64, 0, 1, 1)
BVADD(64, 1, 0, 1)
// Overflow
BVADD(64, UINT64_MAX, 1, 0)
BVADD(64, 1, UINT64_MAX, 0)
BVADD(64, UINT64_MAX, 2, 1)
BVADD(64, 2, UINT64_MAX, 1)
