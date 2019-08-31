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
#include <cmath>

TEST(MakeFromIEEEBitVector, PositiveZeroFloat32) {
  Float32 f(BitVector<32>(0x0));
  ASSERT_EQ(f.getRawData(), 0.0f);
  ASSERT_FALSE(std::signbit(f.getRawData()));
  Float32 zero = Float32::getPositiveZero();
  ASSERT_EQ(zero, f);
}

TEST(MakeFromIEEEBitVector, PositiveZeroFloat64) {
  Float64 f(BitVector<64>(0x0));
  ASSERT_EQ(f.getRawData(), 0.0);
  ASSERT_FALSE(std::signbit(f.getRawData()));
  Float64 zero = Float64::getPositiveZero();
  ASSERT_EQ(zero, f);
}

TEST(MakeFromIEEEBitVector, NegativeZeroFloat32) {
  Float32 f(BitVector<32>(UINT32_C(0x80000000)));
  ASSERT_EQ(f.getRawData(), 0.0f);
  ASSERT_TRUE(std::signbit(f.getRawData()));
  Float32 zero = Float32::getNegativeZero();
  ASSERT_EQ(zero, f);
}

TEST(MakeFromIEEEBitVector, NegativeZeroFloat64) {
  Float64 f(BitVector<64>(UINT64_C(0x8000000000000000)));
  ASSERT_EQ(f.getRawData(), 0.0);
  ASSERT_TRUE(std::signbit(f.getRawData()));
  Float64 zero = Float64::getNegativeZero();
  ASSERT_EQ(zero, f);
}

TEST(MakeFromIEEEBitVector, PositiveInfinityFloat32) {
  Float32 f(BitVector<32>(UINT32_C(0x7f800000)));
  ASSERT_TRUE(std::isinf(f.getRawData()));
  ASSERT_FALSE(std::signbit(f.getRawData()));
  Float32 inf = Float32::getPositiveInfinity();
  ASSERT_EQ(inf, f);
}

TEST(MakeFromIEEEBitVector, PositiveInfinityFloat64) {
  Float64 f(BitVector<64>(UINT64_C(0x7ff0000000000000)));
  ASSERT_TRUE(std::isinf(f.getRawData()));
  ASSERT_FALSE(std::signbit(f.getRawData()));
  Float64 inf = Float64::getPositiveInfinity();
  ASSERT_EQ(inf, f);
}

TEST(MakeFromIEEEBitVector, NegativeInfinityFloat32) {
  Float32 f(BitVector<32>(UINT32_C(0xff800000)));
  ASSERT_TRUE(std::isinf(f.getRawData()));
  ASSERT_TRUE(std::signbit(f.getRawData()));
  Float32 inf = Float32::getNegativeInfinity();
  ASSERT_EQ(inf, f);
}

TEST(MakeFromIEEEBitVector, NegativeInfinityFloat64) {
  Float64 f(BitVector<64>(UINT64_C(0xfff0000000000000)));
  ASSERT_TRUE(std::isinf(f.getRawData()));
  ASSERT_TRUE(std::signbit(f.getRawData()));
  Float64 inf = Float64::getNegativeInfinity();
  ASSERT_EQ(inf, f);
}

TEST(MakeFromIEEEBitVector, NaNFloat32) {
  Float32 f(BitVector<32>(jfs_nr_float32_get_raw_bits(NAN)));
  ASSERT_TRUE(std::isnan(f.getRawData()));
  auto NaN = Float32::getNaN();
  ASSERT_EQ(NaN, f);
}

TEST(MakeFromIEEEBitVector, NaNFloat64) {
  Float64 f(BitVector<64>(jfs_nr_float64_get_raw_bits(NAN)));
  ASSERT_TRUE(std::isnan(f.getRawData()));
  auto NaN = Float64::getNaN();
  ASSERT_EQ(NaN, f);
}

TEST(MakeFromIEEEBitVector, onePointTwoFiveFloat32) {
  Float32 f(BitVector<32>(UINT32_C(0x3fa00000)));
  ASSERT_EQ(f.getRawData(), 1.25f);
}

TEST(MakeFromIEEEBitVector, onePointTwoFiveFloat64) {
  Float64 f(BitVector<64>(UINT64_C(0x3ff4000000000000)));
  ASSERT_EQ(f.getRawData(), 1.25);
}
