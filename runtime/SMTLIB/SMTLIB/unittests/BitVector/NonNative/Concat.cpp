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

TEST(BvConcat, simpleBig) {
  BitVector<64> x(5);
  BitVector<3> y(1);
  EXPECT_EQ(x, 5);
  EXPECT_EQ(y, 1);
  BitVector<67> result = x.concat(y);
  auto data = result.getBuffer();
  ASSERT_EQ(data.getSize(), 9);
  uint8_t expectedData[] = {0b00101001, 0, 0, 0, 0, 0, 0, 0, 0};
  // Do byte-wise comparison
  for (unsigned index = 0; index < data.getSize(); ++index) {
    ASSERT_EQ(data.get()[index], expectedData[index]);
  }
}
