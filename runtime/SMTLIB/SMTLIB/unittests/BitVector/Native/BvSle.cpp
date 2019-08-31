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
#include "SMTLIBRuntimeTestUtil.h"
#include "gtest/gtest.h"

#define BVSLE_BRUTE(N)                                                         \
  TEST(bvsle, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        int64_t xAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(x, N);              \
        int64_t yAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(y, N);              \
        bool expected = xAsSigned <= yAsSigned;                                \
        ASSERT_EQ(xBv.bvsle(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVSLE_BRUTE(1);
BVSLE_BRUTE(2);
BVSLE_BRUTE(3);
BVSLE_BRUTE(4);
BVSLE_BRUTE(5);
BVSLE_BRUTE(6);
BVSLE_BRUTE(7);
BVSLE_BRUTE(8);
BVSLE_BRUTE(9);
BVSLE_BRUTE(10);

#define BVSLE(N, X, Y, E)                                                      \
  TEST(bvsle, Cmp##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvsle(y), E);                                                  \
  }
// Bv64
BVSLE(64, 0, 0, true)
BVSLE(64, 1, 0, false)
BVSLE(64, 0, 1, true)
BVSLE(64, 1, 1, true)
BVSLE(64, UINT64_MAX, 1, true)
