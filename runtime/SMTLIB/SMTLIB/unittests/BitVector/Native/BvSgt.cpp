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

#define BVSGT_BRUTE(N)                                                         \
  TEST(bvsgt, BruteForceBv##N) {                                               \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        int64_t xAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(x, N);              \
        int64_t yAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(y, N);              \
        bool expected = xAsSigned > yAsSigned;                                 \
        ASSERT_EQ(xBv.bvsgt(yBv), expected);                                   \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVSGT_BRUTE(1);
BVSGT_BRUTE(2);
BVSGT_BRUTE(3);
BVSGT_BRUTE(4);
BVSGT_BRUTE(5);
BVSGT_BRUTE(6);
BVSGT_BRUTE(7);
BVSGT_BRUTE(8);
BVSGT_BRUTE(9);
BVSGT_BRUTE(10);

#define BVSGT(N, X, Y, E)                                                      \
  TEST(bvsgt, Cmp##N##_##X##_##Y) {                                            \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvsgt(y), E);                                                  \
  }
// Bv64
BVSGT(64, 0, 0, false)
BVSGT(64, 1, 0, true)
BVSGT(64, 0, 1, false)
BVSGT(64, 1, 1, false)
BVSGT(64, UINT64_MAX, 1, false)
BVSGT(64, 1, UINT64_MAX, true)
