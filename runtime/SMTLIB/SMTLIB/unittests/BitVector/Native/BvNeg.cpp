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

#define BVNEG_BRUTE(N)                                                         \
  TEST(bvneg, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      BitVector<N> xBv(x);                                                     \
      static_assert(N < 64, "not safe");                                       \
      uint64_t mask = (UINT64_C(1) << N) - 1;                                  \
      uint64_t expected = (x == 0) ? (0) : (((~x) & mask) + 1);                \
      EXPECT_EQ(xBv.bvneg(), expected);                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVNEG_BRUTE(1);
BVNEG_BRUTE(2);
BVNEG_BRUTE(3);
BVNEG_BRUTE(4);
BVNEG_BRUTE(5);
BVNEG_BRUTE(6);
BVNEG_BRUTE(7);
BVNEG_BRUTE(8);
BVNEG_BRUTE(9);
BVNEG_BRUTE(10);

#define BVNEG(N, X, E)                                                         \
  TEST(bvneg, BvNeg##N##_##X) {                                                \
    BitVector<N> x(X);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(x.bvneg(), E);                                                   \
  }

// Bv16
BVNEG(16, 0, 0)
BVNEG(16, 1, (UINT64_C(1) << 16) - 1)
BVNEG(16, 2, (UINT64_C(1) << 16) - 2)

// Bv64
BVNEG(64, 0, 0)
BVNEG(64, 1, UINT64_MAX)
BVNEG(64, UINT64_MAX, 1)
// 18446744073709551614 == (UINT64_MAX - 1)
BVNEG(64, 18446744073709551614UL, 2)
