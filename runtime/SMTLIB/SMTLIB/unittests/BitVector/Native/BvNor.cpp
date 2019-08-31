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

#define BVNOR_BRUTE(N)                                                         \
  TEST(bvnor, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t mask = (1 << N) - 1;                                          \
        uint64_t expected = (~(x | y)) & mask;                                 \
        EXPECT_EQ(xBv.bvnor(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVNOR_BRUTE(1);
BVNOR_BRUTE(2);
BVNOR_BRUTE(3);
BVNOR_BRUTE(4);
BVNOR_BRUTE(5);
BVNOR_BRUTE(6);
BVNOR_BRUTE(7);
BVNOR_BRUTE(8);
BVNOR_BRUTE(9);
BVNOR_BRUTE(10);

#define BVNOR(N, X, Y, E)                                                      \
  TEST(bvnor, Nor##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvnor(y), E);                                                  \
  }
// Bv64
BVNOR(64, 0, 0, UINT64_MAX)
BVNOR(64, 8, 9, 0xfffffffffffffff6UL)
