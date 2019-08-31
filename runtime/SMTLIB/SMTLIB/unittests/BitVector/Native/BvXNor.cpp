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

#define BVXNOR_BRUTE(N)                                                        \
  TEST(bvxnor, BruteForceBv##N) {                                              \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t mask = (1 << N) - 1;                                          \
        uint64_t expected = ((~(x ^ y))) & mask;                               \
        EXPECT_EQ(xBv.bvxnor(yBv), expected);                                  \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVXNOR_BRUTE(1);
BVXNOR_BRUTE(2);
BVXNOR_BRUTE(3);
BVXNOR_BRUTE(4);
BVXNOR_BRUTE(5);
BVXNOR_BRUTE(6);
BVXNOR_BRUTE(7);
BVXNOR_BRUTE(8);
BVXNOR_BRUTE(9);
BVXNOR_BRUTE(10);

#define BVXNOR(N, X, Y, E)                                                     \
  TEST(bvxnor, XNor##N##_##X##_##Y) {                                          \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvxnor(y), E);                                                 \
  }
// Bv64
BVXNOR(64, 0, 0, UINT64_MAX)
// UINT64_MAX - 1
BVXNOR(64, 8, 9, 0xfffffffffffffffeUL)
