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

TEST(bvzeroexend, simpleNonNative) {
  BitVector<64> x(255);
  BitVector<67> extended = x.zeroExtend<3>();
  auto rawData = extended.getBuffer();
  ASSERT_EQ(rawData.getSize(), 9);
  ASSERT_EQ(rawData.get()[0], 255);
  for (unsigned index = 1; index < rawData.getSize(); ++index) {
    ASSERT_EQ(rawData.get()[index], 0);
  }
}
