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

#define BVNAND_BRUTE(N)                                                        \
  TEST(bvnand, BruteForceBv##N) {                                              \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        uint64_t mask = (1 << N) - 1;                                          \
        uint64_t expected = (~(x & y)) & mask;                                 \
        EXPECT_EQ(xBv.bvnand(yBv), expected);                                  \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVNAND_BRUTE(1);
BVNAND_BRUTE(2);
BVNAND_BRUTE(3);
BVNAND_BRUTE(4);
BVNAND_BRUTE(5);
BVNAND_BRUTE(6);
BVNAND_BRUTE(7);
BVNAND_BRUTE(8);
BVNAND_BRUTE(9);
BVNAND_BRUTE(10);

#define BVNAND(N, X, Y, E)                                                     \
  TEST(bvnand, Nand##N##_##X##_##Y) {                                          \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvnand(y), E);                                                 \
  }
// Bv64
BVNAND(64, 0, 0, UINT64_MAX)
// Simple and
BVNAND(64, 8, 9, 0xfffffffffffffff7UL)
