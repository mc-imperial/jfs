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

#define BVNOT_BRUTE(N)                                                         \
  TEST(bvnot, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      BitVector<N> xBv(x);                                                     \
      uint64_t mask = (UINT64_C(1) << N) - 1;                                  \
      uint64_t expected = (~x) & mask;                                         \
      EXPECT_EQ(xBv.bvnot(), expected);                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVNOT_BRUTE(1);
BVNOT_BRUTE(2);
BVNOT_BRUTE(3);
BVNOT_BRUTE(4);
BVNOT_BRUTE(5);
BVNOT_BRUTE(6);
BVNOT_BRUTE(7);
BVNOT_BRUTE(8);
BVNOT_BRUTE(9);
BVNOT_BRUTE(10);

#define BVNOT(N, X, E)                                                         \
  TEST(bvnot, Not##N##_##X) {                                                  \
    BitVector<N> x(X);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(x.bvnot(), E);                                                   \
  }
// Bv64
BVNOT(64, 0, UINT64_MAX)
// 18446744073709551615 == UINT64_MAX
BVNOT(64, 18446744073709551615UL, 0)
