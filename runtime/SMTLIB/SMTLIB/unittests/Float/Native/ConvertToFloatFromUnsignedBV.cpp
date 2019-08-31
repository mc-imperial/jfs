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

TEST(ConvertToFloatFromUnsignedBV, zero) {
  ASSERT_TRUE((Float32::convertFromUnsignedBV<32>(JFS_RM_RNE, BitVector<32>(0)))
                  .isZero());
  ASSERT_TRUE((Float64::convertFromUnsignedBV<64>(JFS_RM_RNE, BitVector<64>(0)))
                  .isZero());
}

TEST(ConvertToFloatFromUnsignedBV, TwoFiveSix) {
  ASSERT_EQ(
      (Float32::convertFromUnsignedBV<32>(JFS_RM_RNE, BitVector<32>(256))),
      Float32(256.0f));
  ASSERT_EQ(
      (Float64::convertFromUnsignedBV<32>(JFS_RM_RNE, BitVector<32>(256))),
      Float64(256.0));
}

TEST(ConvertToFloatFromUnsignedBV, Float32RoundedRTE) {
  // These values are derived by running Z3 on the following query
  /*
    (declare-fun a () (_ BitVec 64))
    (define-fun result () (_ FloatingPoint 8 24) ((_ to_fp_unsigned 8 24) RNE
    a))
    (define-fun conv_back () (_ BitVec 64) ((_ fp.to_ubv 64) RNE result))
    (assert (not (fp.isNaN result)))
    (assert (not (= a conv_back)))
    (check-sat)
    (get-value (a))
    (get-value (result))
    (get-value (conv_back))
   */
  BitVector<64> initialValue(UINT64_C(0xfe000f8000000000));
  Float32 value = Float32::convertFromUnsignedBV<64>(JFS_RM_RNE, initialValue);
  ASSERT_EQ(value, Float32(0, 0xbe, UINT32_C(0b11111100000000000010000)));
}

TEST(ConvertToFloatFromUnsignedBV, Float64RoundedRTE) {
  // These values are derived by running Z3 on the following query
  /*
    (declare-fun a () (_ BitVec 64))
    (define-fun result () (_ FloatingPoint 11 53) ((_ to_fp_unsigned 11 53) RNE
    a))
    (define-fun conv_back () (_ BitVec 64) ((_ fp.to_ubv 64) RNE result))
    (assert (not (fp.isNaN result)))
    (assert (not (= a conv_back)))
    (check-sat)
    (get-value (a))
    (get-value (result))
    (get-value (conv_back))
   */
  BitVector<64> initialValue(UINT64_C(0x8000000000000400));
  Float64 value = Float64::convertFromUnsignedBV<64>(JFS_RM_RNE, initialValue);
  ASSERT_EQ(value, Float64(0, 0b10000111110, UINT64_C(0x0000000000000)));
}

// FIXME: Write more tests to test the different rounding modes
