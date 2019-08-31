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

#define BVSMOD(N, X, Y, E)                                                     \
  TEST(bvsmod, SMod##N##_##X##_##Y) {                                          \
    BitVector<N> x(X);                                                         \
    BitVector<N> y(Y);                                                         \
    EXPECT_EQ(x, X);                                                           \
    EXPECT_EQ(y, Y);                                                           \
    EXPECT_EQ(x.bvsmod(y), E);                                                 \
  }

/* NOTE: Can use SMT solver to generate test values
 (declare-fun x () (_ BitVec 3))
 (assert (= x (bvsrem (_ bv7 3) (_ bv5 3))))
 (check-sat)
 (get-model)
*/

// Division by zero
BVSMOD(3, 0, 0, 0)
BVSMOD(3, 1, 0, 1)
BVSMOD(3, 2, 0, 2)
BVSMOD(3, 3, 0, 3)
BVSMOD(3, 4, 0, 4)
BVSMOD(3, 5, 0, 5)
BVSMOD(3, 6, 0, 6)
BVSMOD(3, 7, 0, 7)

// +ve operands
BVSMOD(3, 0, 1, 0)
BVSMOD(3, 1, 1, 0)
BVSMOD(3, 0, 2, 0)
BVSMOD(3, 1, 2, 1)
BVSMOD(3, 2, 2, 0)
BVSMOD(3, 3, 2, 1)

// lhs -ve, rhs +ve
BVSMOD(3, 4, 2, 0)
BVSMOD(3, 5, 2, 1)
BVSMOD(3, 6, 2, 0)
BVSMOD(3, 7, 2, 1)

// lhs +ve, rhs -ve
BVSMOD(3, 0, 5, 0)
BVSMOD(3, 1, 5, 6)
BVSMOD(3, 2, 5, 7)
BVSMOD(3, 3, 5, 0)

// lhs -ve, rhs -ve
BVSMOD(3, 4, 5, 7)
BVSMOD(3, 5, 5, 0)
BVSMOD(3, 6, 5, 6)
BVSMOD(3, 7, 5, 7)
