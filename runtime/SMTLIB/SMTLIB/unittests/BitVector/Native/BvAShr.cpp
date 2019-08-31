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

#define BVASHR_BRUTE(N)                                                        \
  TEST(bvashr, BruteForceBv##N) {                                              \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t mask = (UINT64_C(1) << N) - 1;                                \
        int64_t xAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(x, N);              \
        int64_t yAsSigned =                                                    \
            jfs::smtlib_runtime_test_util::to_signed_value(y, N);              \
        int64_t expected = 0;                                                  \
        if (yAsSigned >= 0 && yAsSigned < N) {                                 \
          expected = (xAsSigned >> yAsSigned);                                 \
        } else if (xAsSigned < 0) {                                            \
          /* SMTLIB's definition means if we overshift the result              \
           * will be all ones */                                               \
          expected = -1;                                                       \
        } else {                                                               \
          /* SMTLIB's definition means if we overshift the result              \
           * will be 0 */                                                      \
          expected = 0;                                                        \
        }                                                                      \
        uint64_t expectedBits =                                                \
            jfs::smtlib_runtime_test_util::to_expected_bits_from_signed_value( \
                expected, N);                                                  \
        BitVector<N> result = xBv.bvashr(yBv);                                 \
        ASSERT_EQ(result, expectedBits);                                       \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVASHR_BRUTE(1);
BVASHR_BRUTE(2);
BVASHR_BRUTE(3);
BVASHR_BRUTE(4);
BVASHR_BRUTE(5);
BVASHR_BRUTE(6);
BVASHR_BRUTE(7);
BVASHR_BRUTE(8);
BVASHR_BRUTE(9);
BVASHR_BRUTE(10);

#define BVASHR(N, X, Y, E)                                                     \
  TEST(bvashr, AShr##N##_##X##_##Y) {                                          \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvashr(y), E);                                                 \
  }
// TODO: Add more tests
