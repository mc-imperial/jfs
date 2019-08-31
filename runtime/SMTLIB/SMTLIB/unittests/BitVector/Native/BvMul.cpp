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

#define BVMUL_BRUTE(N)                                                         \
  TEST(bvmul, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t expected = (x * y) % (1 << N);                                \
        EXPECT_EQ(xBv.bvmul(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVMUL_BRUTE(1);
BVMUL_BRUTE(2);
BVMUL_BRUTE(3);
BVMUL_BRUTE(4);
BVMUL_BRUTE(5);
BVMUL_BRUTE(6);
BVMUL_BRUTE(7);
BVMUL_BRUTE(8);
BVMUL_BRUTE(9);
BVMUL_BRUTE(10);

#define BVMUL(N, X, Y, E)                                                      \
  TEST(bvmul, Mul##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvmul(y), E);                                                  \
  }
// Bv64
BVMUL(64, 0, 0, 0)
// Simple multiplication
BVMUL(64, 0, 1, 0)
BVMUL(64, 1, 0, 0)
BVMUL(64, 1, 1, 1)
BVMUL(64, 2, 1, 2)
BVMUL(64, 1, 2, 2)
// Overflow
BVMUL(64, UINT64_MAX, 2, UINT64_MAX - 1)
BVMUL(64, 2, UINT64_MAX, UINT64_MAX - 1)
BVMUL(64, UINT64_MAX, 3, UINT64_MAX - 2)
BVMUL(64, 3, UINT64_MAX, UINT64_MAX - 2)
