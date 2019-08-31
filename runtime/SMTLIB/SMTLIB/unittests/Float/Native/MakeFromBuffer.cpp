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
#include <math.h>
#include <memory>
#include <string.h>

namespace {
void testFloat32Bits(jfs_nr_float32 initialValue, uint32_t expectedBits) {
  uint8_t buffer[sizeof(jfs_nr_float32)];
  jfs_nr_float32* view = reinterpret_cast<jfs_nr_float32*>(buffer);
  *view = initialValue;
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(jfs_nr_float32));
  Float32 x = makeFloatFrom<8, 24>(bufferRef, 0, 31);
  ASSERT_EQ(x.getRawBits(), expectedBits);
}

void testFloat32Value(jfs_nr_float32 initialValue) {
  uint8_t buffer[sizeof(jfs_nr_float32)];
  jfs_nr_float32* view = reinterpret_cast<jfs_nr_float32*>(buffer);
  *view = initialValue;
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(jfs_nr_float32));
  Float32 x = makeFloatFrom<8, 24>(bufferRef, 0, 31);
  ASSERT_EQ(x.getRawData(), initialValue);
}

void testFloat64Bits(jfs_nr_float64 initialValue, uint64_t expectedBits) {
  uint8_t buffer[sizeof(jfs_nr_float64)];
  jfs_nr_float64* view = reinterpret_cast<jfs_nr_float64*>(buffer);
  *view = initialValue;
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(jfs_nr_float64));
  Float64 x = makeFloatFrom<11, 53>(bufferRef, 0, 63);
  ASSERT_EQ(x.getRawBits(), expectedBits);
}

void testFloat64Value(jfs_nr_float64 initialValue) {
  uint8_t buffer[sizeof(jfs_nr_float64)];
  jfs_nr_float64* view = reinterpret_cast<jfs_nr_float64*>(buffer);
  *view = initialValue;
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(jfs_nr_float64));
  Float64 x = makeFloatFrom<11, 53>(bufferRef, 0, 63);
  ASSERT_EQ(x.getRawData(), initialValue);
}
}

TEST(MakeFromBuffer, PositiveZero) {
  testFloat32Bits(0.0f, UINT32_C(0x0));
  testFloat64Bits(0.0, UINT64_C(0x0));
}

TEST(MakeFromBuffer, NegativeZero) {
  testFloat32Bits(-0.0f, UINT32_C(0x80000000));
  testFloat64Bits(-0.0, UINT64_C(0x8000000000000000));
}

TEST(MakeFromBuffer, PositiveInf) {
  testFloat32Bits(INFINITY, UINT32_C(0x7f800000));
  testFloat64Bits(INFINITY, UINT64_C(0x7ff0000000000000));
}

TEST(MakeFromBuffer, NegativeInf) {
  testFloat32Bits(-INFINITY, UINT32_C(0xff800000));
  testFloat64Bits(-INFINITY, UINT64_C(0xfff0000000000000));
}

TEST(MakeFromBuffer, PositiveOnes) {
  testFloat32Value(1.0f);
  testFloat64Value(1.0);
}

TEST(MakeFromBuffer, NegativeOnes) {
  testFloat32Value(-1.0f);
  testFloat64Value(-1.0);
}

TEST(MakeFromBuffer, NaN) {
  testFloat32Bits(NAN, jfs_nr_float32_get_raw_bits(NAN));
  testFloat64Bits(NAN, jfs_nr_float64_get_raw_bits(NAN));
}

TEST(MakeFromBuffer, simpleValuesFloat32) {
  float values[] = {1.0f, 2.0f, 0.1f, 256.0f};
  uint8_t* view = reinterpret_cast<uint8_t*>(values);
  const size_t viewSize = sizeof(values);
  BufferRef<const uint8_t> bufferRef(view, viewSize);
  Float32 repr[]{
      makeFloatFrom<8, 24>(bufferRef, 0, 31),
      makeFloatFrom<8, 24>(bufferRef, 32, 63),
      makeFloatFrom<8, 24>(bufferRef, 64, 95),
      makeFloatFrom<8, 24>(bufferRef, 96, 127),
  };
  // Check bits
  for (unsigned index = 0; index < sizeof(values) / sizeof(float); ++index) {
    ASSERT_EQ(repr[index].getRawBits(),
              jfs_nr_float32_get_raw_bits(values[index]));
  }
}

TEST(MakeFromBuffer, simpleValuesFloat64) {
  double values[] = {1.0, 2.0, 0.1, 256.0};
  uint8_t* view = reinterpret_cast<uint8_t*>(values);
  const size_t viewSize = sizeof(values);
  BufferRef<const uint8_t> bufferRef(view, viewSize);
  Float64 repr[]{
      makeFloatFrom<11, 53>(bufferRef, 0, 63),
      makeFloatFrom<11, 53>(bufferRef, 64, 127),
      makeFloatFrom<11, 53>(bufferRef, 128, 191),
      makeFloatFrom<11, 53>(bufferRef, 192, 255),
  };
  // Check bits
  for (unsigned index = 0; index < sizeof(values) / sizeof(double); ++index) {
    ASSERT_EQ(repr[index].getRawBits(),
              jfs_nr_float64_get_raw_bits(values[index]));
  }
}
