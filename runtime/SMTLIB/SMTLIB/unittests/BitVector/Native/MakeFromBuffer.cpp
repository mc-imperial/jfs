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
#include <memory>
#include <string.h>

TEST(MakeFromBuffer, WholeBuffer64) {
  uint8_t buffer[sizeof(uint64_t)];
  uint64_t* view = reinterpret_cast<uint64_t*>(buffer);
  *view = UINT64_MAX;
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(uint64_t));
  BitVector<64> x = makeBitVectorFrom<64>(bufferRef, 0, 63);
  ASSERT_EQ(x, UINT64_MAX);
}

TEST(MakeFromBuffer, HalfBuffer64) {
  uint8_t buffer[sizeof(uint64_t)];
  uint64_t* view = reinterpret_cast<uint64_t*>(buffer);
  *view = (UINT64_MAX << 32); // Lower half is zero, upper half is all ones
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(uint64_t));
  BitVector<32> lower = makeBitVectorFrom<32>(bufferRef, 0, 31);
  ASSERT_EQ(lower, 0);
  BitVector<32> upper = makeBitVectorFrom<32>(bufferRef, 32, 63);
  ASSERT_EQ(upper, (UINT64_MAX >> 32));
}

TEST(MakeFromBuffer, IndividualBits) {
  uint8_t buffer[1];
  buffer[0] = 0b10000001;
  BufferRef<const uint8_t> bufferRef(buffer, 1);
#define CHECK_BIT(N, VALUE)                                                    \
  BitVector<1> bit##N = makeBitVectorFrom<1>(bufferRef, N, N);                 \
  ASSERT_EQ(bit##N, VALUE);
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
  BitVector<2> a = makeBitVectorFrom<2>(bufferRef, 7, 8);
  ASSERT_EQ(a, 3);
  BitVector<3> b = makeBitVectorFrom<3>(bufferRef, 7, 9);
  ASSERT_EQ(b, 7);
  BitVector<4> c = makeBitVectorFrom<4>(bufferRef, 7, 10);
  ASSERT_EQ(c, 7);
  BitVector<6> d = makeBitVectorFrom<6>(bufferRef, 10, 15);
  ASSERT_EQ(d, 0);
}

TEST(MakeFromBuffer, LargeBuffer) {
  const size_t numBytes = 128;
  std::unique_ptr<uint8_t, decltype(std::free)*> buffer(
      reinterpret_cast<uint8_t*>(malloc(numBytes)), std::free);
  // All ones
  memset(buffer.get(), 255, numBytes);
  BufferRef<const uint8_t> bufferRef(buffer.get(), numBytes);
  for (unsigned bitOffset = 0; bitOffset <= ((numBytes * 8) - 8); ++bitOffset) {
    BitVector<8> a = makeBitVectorFrom<8>(bufferRef, bitOffset, bitOffset + 7);
    ASSERT_EQ(a, 255);
  }
}

#define MAKE_FROM_LARGE(N, BUFFER_SIZE, ALL_BITS_ONE)                          \
  TEST(MakeFromBuffer, LargeBuffer_##N##_##BUFFER_SIZE##_##ALL_BITS_ONE) {     \
    const size_t numBytes = BUFFER_SIZE;                                       \
    static_assert(BUFFER_SIZE > 0, "invalid buffer size");                     \
    static_assert(N >= 0 && N <= 64, "invalid N value");                       \
    std::unique_ptr<uint8_t, decltype(std::free)*> buffer(                     \
        reinterpret_cast<uint8_t*>(malloc(numBytes)), std::free);              \
    if (ALL_BITS_ONE) {                                                        \
      memset(buffer.get(), 255, numBytes);                                     \
    } else {                                                                   \
      memset(buffer.get(), 0, numBytes);                                       \
    }                                                                          \
    ASSERT_LE(N, 64);                                                          \
    uint64_t maxValue = 0;                                                     \
    if (N >= 64) {                                                             \
      maxValue = UINT64_MAX;                                                   \
    } else {                                                                   \
      maxValue = (UINT64_MAX) >> (64 - N);                                     \
    }                                                                          \
                                                                               \
    BufferRef<const uint8_t> bufferRef(buffer.get(), numBytes);                \
    for (unsigned bitOffset = 0; bitOffset <= ((numBytes * 8) - N);            \
         ++bitOffset) {                                                        \
      const BitVector<N> a =                                                   \
          makeBitVectorFrom<N>(bufferRef, bitOffset, bitOffset + (N - 1));     \
      if (ALL_BITS_ONE) {                                                      \
        ASSERT_EQ(a, maxValue);                                                \
      } else {                                                                 \
        ASSERT_EQ(a, 0);                                                       \
      }                                                                        \
    }                                                                          \
  }
MAKE_FROM_LARGE(64, 1990, true)
MAKE_FROM_LARGE(64, 1990, false)
MAKE_FROM_LARGE(1, 1990, true)
MAKE_FROM_LARGE(1, 1990, false)
MAKE_FROM_LARGE(2, 1990, true)
MAKE_FROM_LARGE(2, 1990, false)
MAKE_FROM_LARGE(3, 1990, true)
MAKE_FROM_LARGE(3, 1990, false)
MAKE_FROM_LARGE(4, 1990, true)
MAKE_FROM_LARGE(4, 1990, false)
