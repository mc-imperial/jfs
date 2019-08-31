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

#define ROTATE_RIGHT_BRUTE(N)                                                  \
  TEST(rotate_right, BruteForceBv##N) {                                        \
    for (unsigned x = 0; x < (1 << N); ++x) {                                  \
      for (unsigned y = 0; y < (1 << N); ++y) {                                \
        BitVector<N> xBv(x);                                                   \
        int originalOneBitCount = __builtin_popcount(x);                       \
        uint64_t mask = (UINT64_C(1) << N) - 1;                                \
        uint64_t shift = y % N;                                                \
        uint64_t expected = ((x >> shift) | (x << (N - shift))) & mask;        \
        BitVector<N> result = xBv.rotate_right(y);                             \
        auto buffer = result.getBuffer();                                      \
        uint64_t resultData = *(reinterpret_cast<uint64_t *>(buffer.get()));   \
        int resultOneBitCount = __builtin_popcount(resultData);                \
        ASSERT_EQ(result, expected);                                           \
        ASSERT_EQ(originalOneBitCount, resultOneBitCount);                     \
      }                                                                        \
    }                                                                          \
  }

// Brute force test the smaller bvs
ROTATE_RIGHT_BRUTE(1);
ROTATE_RIGHT_BRUTE(2);
ROTATE_RIGHT_BRUTE(3);
ROTATE_RIGHT_BRUTE(4);
ROTATE_RIGHT_BRUTE(5);
ROTATE_RIGHT_BRUTE(6);
ROTATE_RIGHT_BRUTE(7);
ROTATE_RIGHT_BRUTE(8);
ROTATE_RIGHT_BRUTE(9);
ROTATE_RIGHT_BRUTE(10);

#define ROTATE_RIGHT(N, X, Y, E)                                               \
  TEST(rotate_right, Rot_##N##_##X##_##Y) {                                    \
    int originalOneBitCount = __builtin_popcount(X);                           \
    BitVector<N> x(X);                                                         \
    ASSERT_EQ(x, X);                                                           \
    BitVector<N> result = x.rotate_right(Y);                                   \
    auto buffer = result.getBuffer();                                          \
    ASSERT_EQ(buffer.getSize(), sizeof(uint64_t));                             \
    uint64_t resultData = *(reinterpret_cast<uint64_t *>(buffer.get()));       \
    int resultOneBitCount = __builtin_popcount(resultData);                    \
    ASSERT_EQ(result, E);                                                      \
    /* check we didn't loose any bits */                                       \
    ASSERT_EQ(originalOneBitCount, resultOneBitCount);                         \
  }

// Bv4
// Rotation of zero does nothing
ROTATE_RIGHT(4, 0, 0, 0)
ROTATE_RIGHT(4, 0, 1, 0)
ROTATE_RIGHT(4, 0, 2, 0)
ROTATE_RIGHT(4, 0, 3, 0)
ROTATE_RIGHT(4, 0, 4, 0)
ROTATE_RIGHT(4, 0, 5, 0)

// Rotate single bit
ROTATE_RIGHT(4, 1, 0, 1)
ROTATE_RIGHT(4, 1, 1, 8)
ROTATE_RIGHT(4, 1, 2, 4)
ROTATE_RIGHT(4, 1, 3, 2)
ROTATE_RIGHT(4, 1, 4, 1)

// Rotate 0b1001
ROTATE_RIGHT(4, 0b1001, 0, 0b1001)
ROTATE_RIGHT(4, 0b1001, 1, 0b1100)
ROTATE_RIGHT(4, 0b1001, 2, 0b0110)
ROTATE_RIGHT(4, 0b1001, 3, 0b0011)
ROTATE_RIGHT(4, 0b1001, 4, 0b1001)

// TODO: Write more tests
