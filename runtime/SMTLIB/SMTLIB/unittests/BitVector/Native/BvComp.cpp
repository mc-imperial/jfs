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

#define BVCOMP_BRUTE(N)                                                        \
  TEST(bvcomp, BruteForceBv##N) {                                              \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        BitVector<N> yBv(y);                                                   \
        if (x == y) {                                                          \
          ASSERT_EQ(xBv.bvcomp(yBv), BitVector<1>(1));                         \
        } else {                                                               \
          ASSERT_EQ(xBv.bvcomp(yBv), BitVector<1>(0));                         \
        }                                                                      \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
BVCOMP_BRUTE(1);
BVCOMP_BRUTE(2);
BVCOMP_BRUTE(3);
BVCOMP_BRUTE(4);
BVCOMP_BRUTE(5);
BVCOMP_BRUTE(6);
BVCOMP_BRUTE(7);
BVCOMP_BRUTE(8);
BVCOMP_BRUTE(9);
BVCOMP_BRUTE(10);
