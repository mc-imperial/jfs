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

#define BVSLT_BRUTE(N)                                                         \
  TEST(bvslt, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        int64_t xAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(x, N);              \
        int64_t yAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(y, N);              \
        bool expected = xAsSigned < yAsSigned;                                 \
        ASSERT_EQ(xBv.bvslt(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVSLT_BRUTE(1);
BVSLT_BRUTE(2);
BVSLT_BRUTE(3);
BVSLT_BRUTE(4);
BVSLT_BRUTE(5);
BVSLT_BRUTE(6);
BVSLT_BRUTE(7);
BVSLT_BRUTE(8);
BVSLT_BRUTE(9);
BVSLT_BRUTE(10);

#define BVSLT(N, X, Y, E)                                                      \
  TEST(bvslt, Cmp##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvslt(y), E);                                                  \
  }
// Bv64
BVSLT(64, 0, 0, false)
BVSLT(64, 1, 0, false)
BVSLT(64, 0, 1, true)
BVSLT(64, 1, 1, false)
BVSLT(64, UINT64_MAX, 1, true)
