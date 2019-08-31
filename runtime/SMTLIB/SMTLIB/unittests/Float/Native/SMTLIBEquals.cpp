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
#include "SMTLIB/Float.h"
#include "gtest/gtest.h"

namespace {

template <typename T> void checkDisjointConstantsDisjoint() {
  T values[] = {T::getPositiveZero(),
                T::getNegativeZero(),
                T::getPositiveInfinity(),
                T::getNegativeInfinity(),
                T::getNaN(),
                T(1.5),
                T(-1.5)};
  for (unsigned index = 0; index < sizeof(values) / sizeof(T); ++index) {
    for (unsigned indexOther = 0; indexOther < sizeof(values) / sizeof(T);
         ++indexOther) {
      if (index == indexOther) {
        ASSERT_TRUE(values[index] == values[indexOther]);
      } else {
        ASSERT_FALSE(values[index] == values[indexOther]);
      }
    }
  }
}
}

TEST(SMTLIBEquals, DisjointConstantsDisjointFloat32) {
  checkDisjointConstantsDisjoint<Float32>();
}

TEST(SMTLIBEquals, DisjointConstantsDisjointFloat64) {
  checkDisjointConstantsDisjoint<Float64>();
}
