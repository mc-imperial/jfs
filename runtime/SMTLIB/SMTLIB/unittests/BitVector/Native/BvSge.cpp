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

#define BVSGE_BRUTE(N)                                                         \
  TEST(bvsge, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        int64_t xAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(x, N);              \
        int64_t yAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(y, N);              \
        bool expected = xAsSigned >= yAsSigned;                                \
        ASSERT_EQ(xBv.bvsge(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVSGE_BRUTE(1);
BVSGE_BRUTE(2);
BVSGE_BRUTE(3);
BVSGE_BRUTE(4);
BVSGE_BRUTE(5);
BVSGE_BRUTE(6);
BVSGE_BRUTE(7);
BVSGE_BRUTE(8);
BVSGE_BRUTE(9);
BVSGE_BRUTE(10);

#define BVSGE(N, X, Y, E)                                                      \
  TEST(bvsge, Cmp##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvsge(y), E);                                                  \
  }
// Bv64
BVSGE(64, 0, 0, true)
BVSGE(64, 1, 0, true)
BVSGE(64, 0, 1, false)
BVSGE(64, 1, 1, true)
BVSGE(64, UINT64_MAX, 1, false)
BVSGE(64, 1, UINT64_MAX, true)
