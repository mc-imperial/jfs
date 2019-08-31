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

uint64_t getNegBits(uint64_t v, uint64_t N) {
  uint64_t mask = (UINT64_C(1) << N) - 1;
  return ((~v) + 1) & mask;
}

// FIXME: Use
// jfs::smtlib_runtime_test_util::to_expected_bits_from_signed_value()
#define BVSDIV_BRUTE(N)                                                        \
  TEST(bvsdiv, BruteForceBv##N) {                                              \
    assert(N < 64 && "too many bits");                                         \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t mask = (UINT64_C(1) << N) - 1;                                \
        int64_t negativeMSB = (int64_t(UINT64_C(1) << (N - 1))) * -1;          \
        uint64_t maskOnlyPositiveBits = mask >> 1;                             \
        int64_t xAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(x, N);              \
        int64_t yAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(y, N);              \
        /* SMT-LIB returns all ones if division by zero with bvudiv but        \
           their definition means that if the dividend is negative then the    \
           result of bvudiv gets negated giving `1`.*/                         \
        int64_t divByZeroRetValue =                                            \
            (xAsSigned < 0) ? 1 : ((UINT64_C(1) << N) - 1);                    \
        int64_t expected =                                                     \
            (yAsSigned == 0) ? divByZeroRetValue : (xAsSigned / yAsSigned);    \
        uint64_t expectedBits = (expected < 0) ? getNegBits(expected * -1, N)  \
                                               : ((uint64_t)expected);         \
        BitVector<N> result = xBv.bvsdiv(yBv);                                 \
        EXPECT_EQ(result, expectedBits);                                       \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVSDIV_BRUTE(1);
BVSDIV_BRUTE(2);
BVSDIV_BRUTE(3);
BVSDIV_BRUTE(4);
BVSDIV_BRUTE(5);
BVSDIV_BRUTE(6);
BVSDIV_BRUTE(7);
BVSDIV_BRUTE(8);
BVSDIV_BRUTE(9);
BVSDIV_BRUTE(10);

#define BVSDIV(N, X, Y, E)                                                     \
  TEST(bvsdiv, SDiv##N##_##X##_##Y) {                                          \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvsdiv(y), E);                                                 \
  }
// TODO: Test some values using the macro
