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

void testFloat32Bits(jfs_nr_bitvector_ty sign, jfs_nr_bitvector_ty exponent,
                     jfs_nr_bitvector_ty significand,
                     jfs_nr_bitvector_ty expectedBits) {
  BitVector<1> signBv(sign);
  BitVector<8> exponentBv(exponent);
  BitVector<23> significandBv(significand);
  Float32 repr = Float32(signBv, exponentBv, significandBv);
  ASSERT_EQ(repr.getRawBits(), expectedBits);
}

void testFloat64Bits(jfs_nr_bitvector_ty sign, jfs_nr_bitvector_ty exponent,
                     jfs_nr_bitvector_ty significand,
                     jfs_nr_bitvector_ty expectedBits) {
  BitVector<1> signBv(sign);
  BitVector<11> exponentBv(exponent);
  BitVector<52> significandBv(significand);
  Float64 repr = Float64(signBv, exponentBv, significandBv);
  ASSERT_EQ(repr.getRawBits(), expectedBits);
}
}

TEST(MakeFromTriple, PositiveZero) {
  testFloat32Bits(0, 0, 0, UINT64_C(0x0));
  testFloat64Bits(0, 0, 0, UINT64_C(0x0));
}

TEST(MakeFromTriple, NegativeZero) {
  testFloat32Bits(1, 0, 0, UINT64_C(0x80000000));
  testFloat64Bits(1, 0, 0, UINT64_C(0x8000000000000000));
}

TEST(MakeFromTriple, PositiveInf) {
  testFloat32Bits(0, UINT64_C(0xff), UINT64_C(0), UINT32_C(0x7f800000));
  testFloat64Bits(0, UINT64_C(0x7ff), UINT64_C(0),
                  UINT64_C(0x7ff0000000000000));
}

TEST(MakeFromTriple, NegativeInf) {
  testFloat32Bits(1, UINT64_C(0xff), UINT64_C(0), UINT32_C(0xff800000));
  testFloat64Bits(1, UINT64_C(0x7ff), UINT64_C(0),
                  UINT64_C(0xfff0000000000000));
}

TEST(MakeFromTriple, PositiveOne) {
  testFloat32Bits(0, UINT64_C(0x7f), 0, UINT64_C(0x3f800000));
  testFloat64Bits(0, UINT64_C(0x3ff), 0, UINT64_C(0x3ff0000000000000));
}

TEST(MakeFromTriple, NegativeOne) {
  testFloat32Bits(1, UINT64_C(0x7f), 0, UINT64_C(0xbf800000));
  testFloat64Bits(1, UINT64_C(0x3ff), 0, UINT64_C(0xbff0000000000000));
}

TEST(MakeFromTriple, NaN) {
  testFloat32Bits(0, UINT64_C(0xff), UINT64_C(1), UINT32_C(0x7f800001));
  testFloat64Bits(0, UINT64_C(0x7ff), UINT64_C(1),
                  UINT64_C(0x7ff0000000000001));
}

TEST(MakeFromTriple, OnePointTwoFive) {
  testFloat32Bits(0, UINT64_C(0x7f), UINT64_C(0x200000), UINT64_C(0x3fa00000));
  testFloat64Bits(0, UINT64_C(0x3ff), UINT64_C(0x4000000000000),
                  UINT64_C(0x3ff4000000000000));
}
