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
#include "SMTLIB/Core.h"
#include "gtest/gtest.h"

TEST(MakeFromBuffer, singleBitFromUniformBuffer) {
  uint8_t buffer[sizeof(uint64_t)];
  uint64_t* view = reinterpret_cast<uint64_t*>(buffer);
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(uint64_t));
#define TEST_MAKE_BOOL(L, B, VALUE)                                            \
  bool test_##L##_##B = makeBoolFrom(bufferRef, L, B);                         \
  ASSERT_EQ(test_##L##_##B, VALUE);

  for (unsigned i = 0; i < 2; ++i) {
    bool expected;
    if (i == 0) {
      expected = false;
      // All zeros
      *view = 0;
    } else {
      expected = true;
      // All ones
      *view = UINT64_MAX;
    }

    TEST_MAKE_BOOL(0, 0, expected);
    TEST_MAKE_BOOL(1, 1, expected);
    TEST_MAKE_BOOL(2, 2, expected);
    TEST_MAKE_BOOL(3, 3, expected);
    TEST_MAKE_BOOL(4, 4, expected);
    TEST_MAKE_BOOL(5, 5, expected);
    TEST_MAKE_BOOL(6, 6, expected);
    TEST_MAKE_BOOL(7, 7, expected);
    TEST_MAKE_BOOL(8, 8, expected);
    TEST_MAKE_BOOL(9, 9, expected);
    TEST_MAKE_BOOL(10, 10, expected);
    TEST_MAKE_BOOL(11, 11, expected);
    TEST_MAKE_BOOL(12, 12, expected);
    TEST_MAKE_BOOL(13, 13, expected);
    TEST_MAKE_BOOL(14, 14, expected);
    TEST_MAKE_BOOL(15, 15, expected);
    TEST_MAKE_BOOL(16, 16, expected);
    TEST_MAKE_BOOL(17, 17, expected);
    TEST_MAKE_BOOL(18, 18, expected);
    TEST_MAKE_BOOL(19, 19, expected);
    TEST_MAKE_BOOL(20, 20, expected);
    TEST_MAKE_BOOL(21, 21, expected);
    TEST_MAKE_BOOL(22, 22, expected);
    TEST_MAKE_BOOL(23, 23, expected);
    TEST_MAKE_BOOL(24, 24, expected);
    TEST_MAKE_BOOL(25, 25, expected);
    TEST_MAKE_BOOL(26, 26, expected);
    TEST_MAKE_BOOL(27, 27, expected);
    TEST_MAKE_BOOL(28, 28, expected);
    TEST_MAKE_BOOL(29, 29, expected);
    TEST_MAKE_BOOL(30, 30, expected);
    TEST_MAKE_BOOL(31, 31, expected);
    TEST_MAKE_BOOL(32, 32, expected);
    TEST_MAKE_BOOL(33, 33, expected);
    TEST_MAKE_BOOL(34, 34, expected);
    TEST_MAKE_BOOL(35, 35, expected);
    TEST_MAKE_BOOL(36, 36, expected);
    TEST_MAKE_BOOL(37, 37, expected);
    TEST_MAKE_BOOL(38, 38, expected);
    TEST_MAKE_BOOL(39, 39, expected);
    TEST_MAKE_BOOL(40, 40, expected);
    TEST_MAKE_BOOL(41, 41, expected);
    TEST_MAKE_BOOL(42, 42, expected);
    TEST_MAKE_BOOL(43, 43, expected);
    TEST_MAKE_BOOL(44, 44, expected);
    TEST_MAKE_BOOL(45, 45, expected);
    TEST_MAKE_BOOL(46, 46, expected);
    TEST_MAKE_BOOL(47, 47, expected);
    TEST_MAKE_BOOL(48, 48, expected);
    TEST_MAKE_BOOL(49, 49, expected);
    TEST_MAKE_BOOL(50, 50, expected);
    TEST_MAKE_BOOL(51, 51, expected);
    TEST_MAKE_BOOL(52, 52, expected);
    TEST_MAKE_BOOL(53, 53, expected);
    TEST_MAKE_BOOL(54, 54, expected);
    TEST_MAKE_BOOL(55, 55, expected);
    TEST_MAKE_BOOL(56, 56, expected);
    TEST_MAKE_BOOL(57, 57, expected);
    TEST_MAKE_BOOL(58, 58, expected);
    TEST_MAKE_BOOL(59, 59, expected);
    TEST_MAKE_BOOL(60, 60, expected);
    TEST_MAKE_BOOL(61, 61, expected);
    TEST_MAKE_BOOL(62, 62, expected);
    TEST_MAKE_BOOL(63, 63, expected);
  }
#undef TEST_MAKE_BOOL
}

TEST(MakeFromBuffer, IndividualBits) {
  uint8_t buffer[1];
  buffer[0] = 0b10000001;
  BufferRef<const uint8_t> bufferRef(buffer, 1);
#define CHECK_BIT(N, VALUE)                                                    \
  bool bit##N = makeBoolFrom(bufferRef, N, N);                                 \
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

TEST(MakeFromBuffer, AcrossByteBoundaryFalse) {
  uint8_t buffer[2];
  buffer[0] = 0b00000000;
  buffer[1] = 0b11111110;
  BufferRef<const uint8_t> bufferRef(buffer, 2);
  bool bits = makeBoolFrom(bufferRef, 7, 7);
  ASSERT_EQ(bits, false);
  bool bits2 = makeBoolFrom(bufferRef, 7, 8);
  ASSERT_EQ(bits2, false);
  bool bits3 = makeBoolFrom(bufferRef, 7, 9);
  ASSERT_EQ(bits3, true);
}

#define MAKE_FROM_LARGE(N, BUFFER_SIZE, ALL_BITS_ONE)                          \
  TEST(MakeFromBuffer, LargeBuffer_##N##_##BUFFER_SIZE##_##ALL_BITS_ONE) {     \
    static_assert(BUFFER_SIZE > 0, "invalid buffer size");                     \
    static_assert(N <= 8 && N >= 0, "invalid N value");                        \
    const size_t numBytes = BUFFER_SIZE;                                       \
    std::unique_ptr<uint8_t, decltype(std::free)*> buffer(                     \
        reinterpret_cast<uint8_t*>(malloc(numBytes)), std::free);              \
    if (ALL_BITS_ONE) {                                                        \
      memset(buffer.get(), 255, numBytes);                                     \
    } else {                                                                   \
      memset(buffer.get(), 0, numBytes);                                       \
    }                                                                          \
    BufferRef<const uint8_t> bufferRef(buffer.get(), numBytes);                \
    for (unsigned bitOffset = 0; bitOffset <= ((numBytes * 8) - N);            \
         ++bitOffset) {                                                        \
      bool a = makeBoolFrom(bufferRef, bitOffset, bitOffset + (N - 1));        \
      if (ALL_BITS_ONE) {                                                      \
        ASSERT_EQ(a, true);                                                    \
      } else {                                                                 \
        ASSERT_EQ(a, false);                                                   \
      }                                                                        \
    }                                                                          \
  }
MAKE_FROM_LARGE(1, 1024, true)
MAKE_FROM_LARGE(2, 1024, true)
MAKE_FROM_LARGE(3, 1024, true)
MAKE_FROM_LARGE(4, 1024, true)
MAKE_FROM_LARGE(5, 1024, true)
MAKE_FROM_LARGE(6, 1024, true)
MAKE_FROM_LARGE(7, 1024, true)
MAKE_FROM_LARGE(8, 1024, true)
MAKE_FROM_LARGE(1, 1024, false)
MAKE_FROM_LARGE(2, 1024, false)
MAKE_FROM_LARGE(3, 1024, false)
MAKE_FROM_LARGE(4, 1024, false)
MAKE_FROM_LARGE(5, 1024, false)
MAKE_FROM_LARGE(6, 1024, false)
MAKE_FROM_LARGE(7, 1024, false)
MAKE_FROM_LARGE(8, 1024, false)
