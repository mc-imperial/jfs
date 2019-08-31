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

#define BVXOR_BRUTE(N)                                                         \
  TEST(bvxor, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t mask = (1 << N) - 1;                                          \
        uint64_t expected = ((x ^ y)) & mask;                                  \
        EXPECT_EQ(xBv.bvxor(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVXOR_BRUTE(1);
BVXOR_BRUTE(2);
BVXOR_BRUTE(3);
BVXOR_BRUTE(4);
BVXOR_BRUTE(5);
BVXOR_BRUTE(6);
BVXOR_BRUTE(7);
BVXOR_BRUTE(8);
BVXOR_BRUTE(9);
BVXOR_BRUTE(10);

#define BVXOR(N, X, Y, E)                                                      \
  TEST(bvxor, Xor##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvxor(y), E);                                                  \
  }
// Bv64
BVXOR(64, 0, 0, 0)
BVXOR(64, 8, 9, 1)
