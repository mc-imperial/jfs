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

#define BV_ZERO_EXTEND_BRUTE(N, E)                                             \
  TEST(bvzeroextend, BruteForceBv##N##_##E) {                                  \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      BitVector<N> xBv(x);                                                     \
      static_assert((N + E) < 64, "not safe");                                 \
      uint64_t mask = (UINT64_C(1) << (N + E)) - 1;                            \
      uint64_t expected = x & mask;                                            \
      BitVector<N + E> result = xBv.zeroExtend<E>();                           \
      EXPECT_EQ(result, expected);                                             \
    }                                                                          \
  }

BV_ZERO_EXTEND_BRUTE(1, 0)
BV_ZERO_EXTEND_BRUTE(1, 1)
BV_ZERO_EXTEND_BRUTE(1, 2)
BV_ZERO_EXTEND_BRUTE(1, 3)
BV_ZERO_EXTEND_BRUTE(1, 4)
BV_ZERO_EXTEND_BRUTE(1, 5)
BV_ZERO_EXTEND_BRUTE(1, 6)
BV_ZERO_EXTEND_BRUTE(1, 7)
BV_ZERO_EXTEND_BRUTE(1, 8)
BV_ZERO_EXTEND_BRUTE(2, 0)
BV_ZERO_EXTEND_BRUTE(2, 1)
BV_ZERO_EXTEND_BRUTE(2, 2)
BV_ZERO_EXTEND_BRUTE(2, 3)
BV_ZERO_EXTEND_BRUTE(2, 4)
BV_ZERO_EXTEND_BRUTE(2, 5)
BV_ZERO_EXTEND_BRUTE(2, 6)
BV_ZERO_EXTEND_BRUTE(2, 7)
BV_ZERO_EXTEND_BRUTE(2, 8)
BV_ZERO_EXTEND_BRUTE(3, 0)
BV_ZERO_EXTEND_BRUTE(3, 1)
BV_ZERO_EXTEND_BRUTE(3, 2)
BV_ZERO_EXTEND_BRUTE(3, 3)
BV_ZERO_EXTEND_BRUTE(3, 4)
BV_ZERO_EXTEND_BRUTE(3, 5)
BV_ZERO_EXTEND_BRUTE(3, 6)
BV_ZERO_EXTEND_BRUTE(3, 7)
BV_ZERO_EXTEND_BRUTE(3, 8)
BV_ZERO_EXTEND_BRUTE(4, 0)
BV_ZERO_EXTEND_BRUTE(4, 1)
BV_ZERO_EXTEND_BRUTE(4, 2)
BV_ZERO_EXTEND_BRUTE(4, 3)
BV_ZERO_EXTEND_BRUTE(4, 4)
BV_ZERO_EXTEND_BRUTE(4, 5)
BV_ZERO_EXTEND_BRUTE(4, 6)
BV_ZERO_EXTEND_BRUTE(4, 7)
BV_ZERO_EXTEND_BRUTE(4, 8)
BV_ZERO_EXTEND_BRUTE(5, 0)
BV_ZERO_EXTEND_BRUTE(5, 1)
BV_ZERO_EXTEND_BRUTE(5, 2)
BV_ZERO_EXTEND_BRUTE(5, 3)
BV_ZERO_EXTEND_BRUTE(5, 4)
BV_ZERO_EXTEND_BRUTE(5, 5)
BV_ZERO_EXTEND_BRUTE(5, 6)
BV_ZERO_EXTEND_BRUTE(5, 7)
BV_ZERO_EXTEND_BRUTE(5, 8)
BV_ZERO_EXTEND_BRUTE(6, 0)
BV_ZERO_EXTEND_BRUTE(6, 1)
BV_ZERO_EXTEND_BRUTE(6, 2)
BV_ZERO_EXTEND_BRUTE(6, 3)
BV_ZERO_EXTEND_BRUTE(6, 4)
BV_ZERO_EXTEND_BRUTE(6, 5)
BV_ZERO_EXTEND_BRUTE(6, 6)
BV_ZERO_EXTEND_BRUTE(6, 7)
BV_ZERO_EXTEND_BRUTE(6, 8)
BV_ZERO_EXTEND_BRUTE(7, 0)
BV_ZERO_EXTEND_BRUTE(7, 1)
BV_ZERO_EXTEND_BRUTE(7, 2)
BV_ZERO_EXTEND_BRUTE(7, 3)
BV_ZERO_EXTEND_BRUTE(7, 4)
BV_ZERO_EXTEND_BRUTE(7, 5)
BV_ZERO_EXTEND_BRUTE(7, 6)
BV_ZERO_EXTEND_BRUTE(7, 7)
BV_ZERO_EXTEND_BRUTE(7, 8)
BV_ZERO_EXTEND_BRUTE(8, 0)
BV_ZERO_EXTEND_BRUTE(8, 1)
BV_ZERO_EXTEND_BRUTE(8, 2)
BV_ZERO_EXTEND_BRUTE(8, 3)
BV_ZERO_EXTEND_BRUTE(8, 4)
BV_ZERO_EXTEND_BRUTE(8, 5)
BV_ZERO_EXTEND_BRUTE(8, 6)
BV_ZERO_EXTEND_BRUTE(8, 7)
BV_ZERO_EXTEND_BRUTE(8, 8)
