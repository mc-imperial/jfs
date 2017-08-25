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
#include "SMTLIB/Float.h"
#include "gtest/gtest.h"
#include <math.h>
#include <memory>
#include <string.h>

namespace {
void testFloat32(jfs_nr_float32 initialValue, uint32_t expectedBits) {
  uint8_t buffer[sizeof(jfs_nr_float32)];
  jfs_nr_float32* view = reinterpret_cast<jfs_nr_float32*>(buffer);
  *view = initialValue;
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(jfs_nr_float32));
  Float32 x = makeFloatFrom<8, 24>(bufferRef, 0, 31);
  ASSERT_EQ(x.getRawBits(), expectedBits);
}

void testFloat64(jfs_nr_float64 initialValue, uint64_t expectedBits) {
  uint8_t buffer[sizeof(jfs_nr_float64)];
  jfs_nr_float64* view = reinterpret_cast<jfs_nr_float64*>(buffer);
  *view = initialValue;
  BufferRef<const uint8_t> bufferRef(buffer, sizeof(jfs_nr_float64));
  Float64 x = makeFloatFrom<11, 53>(bufferRef, 0, 63);
  ASSERT_EQ(x.getRawBits(), expectedBits);
}
}

TEST(MakeFromBuffer, PositiveZero) {
  testFloat32(0.0f, UINT32_C(0x0));
  testFloat64(0.0f, UINT64_C(0x0));
}

TEST(MakeFromBuffer, NegativeZero) {
  testFloat32(-0.0f, UINT32_C(0x80000000));
  testFloat64(-0.0, UINT64_C(0x8000000000000000));
}
