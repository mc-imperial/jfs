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

#define BVSREM(N, X, Y, E)                                                     \
  TEST(bvsrem, SRem##N##_##X##_##Y) {                                          \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvsrem(y), E);                                                 \
  }

/* NOTE: Can use SMT solver to generate test values
 (declare-fun x () (_ BitVec 3))
 (assert (= x (bvsrem (_ bv7 3) (_ bv5 3))))
 (check-sat)
 (get-model)
*/

// Division by zero
BVSREM(3, 0, 0, 0)
BVSREM(3, 1, 0, 1)
BVSREM(3, 2, 0, 2)
BVSREM(3, 3, 0, 3)
BVSREM(3, 4, 0, 4)
BVSREM(3, 5, 0, 5)
BVSREM(3, 6, 0, 6)
BVSREM(3, 7, 0, 7)

// +ve operands
BVSREM(3, 0, 1, 0)
BVSREM(3, 1, 1, 0)
BVSREM(3, 0, 2, 0)
BVSREM(3, 1, 2, 1)
BVSREM(3, 2, 2, 0)
BVSREM(3, 3, 2, 1)

// lhs -ve, rhs +ve
BVSREM(3, 4, 2, 0)
BVSREM(3, 5, 2, 7)
BVSREM(3, 6, 2, 0)
BVSREM(3, 7, 2, 7)

// lhs +ve, rhs -ve
BVSREM(3, 0, 5, 0)
BVSREM(3, 1, 5, 1)
BVSREM(3, 2, 5, 2)
BVSREM(3, 3, 5, 0)

// lhs -ve, rhs -ve
BVSREM(3, 4, 5, 7)
BVSREM(3, 5, 5, 0)
BVSREM(3, 6, 5, 6)
BVSREM(3, 7, 5, 7)
