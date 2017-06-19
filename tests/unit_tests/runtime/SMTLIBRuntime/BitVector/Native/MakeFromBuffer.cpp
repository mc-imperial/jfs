//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "SMTLIB/BitVector.h"
#include "gtest/gtest.h"
#include <string.h>

TEST(MakeFromBuffer, WholeBuffer64) {
  uint8_t buffer[sizeof(uint64_t)];
  uint64_t* view = reinterpret_cast<uint64_t*>(buffer);
  *view = UINT64_MAX;
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(uint64_t));
  BitVector<64> x = makeBitVectorFrom<0,63>(bufferRef);
  ASSERT_EQ(x, UINT64_MAX);
}

TEST(MakeFromBuffer, HalfBuffer64) {
  uint8_t buffer[sizeof(uint64_t)];
  uint64_t* view = reinterpret_cast<uint64_t*>(buffer);
  *view = (UINT64_MAX << 32); // Lower half is zero, upper half is all ones
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(uint64_t));
  BitVector<32> lower = makeBitVectorFrom<0, 31>(bufferRef);
  ASSERT_EQ(lower, 0);
  BitVector<32> upper = makeBitVectorFrom<32, 63>(bufferRef);
  ASSERT_EQ(upper, (UINT64_MAX >> 32));
}

TEST(MakeFromBuffer, IndividualBits) {
  uint8_t buffer[1];
  buffer[0] = 0b10000001;
  BufferRef<const uint8_t> bufferRef(buffer, 1);
#define CHECK_BIT(N, VALUE) BitVector<1> bit ## N = makeBitVectorFrom<N, N>(bufferRef); \
  ASSERT_EQ(bit ## N, VALUE);
  CHECK_BIT(0, 1)
  CHECK_BIT(1, 0)
  CHECK_BIT(2, 0)
  CHECK_BIT(3, 0)
  CHECK_BIT(4, 0)
  CHECK_BIT(5, 0)
  CHECK_BIT(6, 0)
  CHECK_BIT(7, 1)
#undef CHECK_BIT
}

TEST(MakeFromBuffer, NonByteAlignedOffset) {
  uint8_t buffer[2];
  buffer[0] = 0b11111111;
  buffer[1] = 0b00000011;
  BufferRef<const uint8_t> bufferRef(buffer, 2);
  BitVector<2> a = makeBitVectorFrom<7,8>(bufferRef);
  ASSERT_EQ(a, 3);
  BitVector<3> b = makeBitVectorFrom<7,9>(bufferRef);
  ASSERT_EQ(b, 7);
  BitVector<4> c = makeBitVectorFrom<7,10>(bufferRef);
  ASSERT_EQ(c, 7);
  BitVector<6> d = makeBitVectorFrom<10,15>(bufferRef);
  ASSERT_EQ(d, 0);
}
