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

TEST(bvsignextend, simpleZeroExt) {
  BitVector<64> a(1);
  BitVector<65> b = a.signExtend<1>();
  auto buffer = b.getBuffer();
  ASSERT_EQ(buffer.getSize(), 9);
  ASSERT_EQ(buffer.get()[0], 0x01);
  for (unsigned index = 1; index < buffer.getSize(); ++index) {
    ASSERT_EQ(buffer.get()[index], 0x00);
  }
}

TEST(bvsignextend, simpleSignExt) {
  BitVector<64> a(UINT64_MAX);
  BitVector<65> b = a.signExtend<1>();
  auto buffer = b.getBuffer();
  ASSERT_EQ(buffer.getSize(), 9);
  for (unsigned index = 0; index < (buffer.getSize() - 1); ++index) {
    ASSERT_EQ(buffer.get()[index], 0xff);
  }
  // 65th bit is one but the rest should be zero inside the buffer.
  ASSERT_EQ(buffer.get()[buffer.getSize() - 1], 0x01);
}
