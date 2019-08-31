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

#define EQ_BRUTE(N)                                                            \
  TEST(bveq, BruteForceBv##N) {                                                \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        if (x == y) {                                                          \
          ASSERT_TRUE(xBv == yBv);                                             \
        } else {                                                               \
          ASSERT_TRUE(!(xBv == yBv));                                          \
        }                                                                      \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
EQ_BRUTE(1);
EQ_BRUTE(2);
EQ_BRUTE(3);
EQ_BRUTE(4);
EQ_BRUTE(5);
EQ_BRUTE(6);
EQ_BRUTE(7);
EQ_BRUTE(8);
EQ_BRUTE(9);
EQ_BRUTE(10);
