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

TEST(ConvertToFloatFromFloat, NaN) {
  ASSERT_TRUE(((Float32::getNaN()).convertToFloat<11, 53>(JFS_RM_RNE)).isNaN());
  // No-op
  ASSERT_TRUE(((Float32::getNaN()).convertToFloat<8, 24>(JFS_RM_RNE)).isNaN());

  ASSERT_TRUE(((Float64::getNaN()).convertToFloat<8, 24>(JFS_RM_RNE)).isNaN());
  // No-op
  ASSERT_TRUE(((Float64::getNaN()).convertToFloat<11, 53>(JFS_RM_RNE)).isNaN());
}

TEST(ConvertToFloatFromFloat, Float64ToFloat32_Diff_RNE_RTP) {
  // These values are derived from a Z3 model run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (define-fun result_rne () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RNE a))
    (define-fun result_rtp () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTP a))
    (assert (not (fp.isNaN a)))
    (assert
      (not
        (fp.eq
          result_rne
          result_rtp
        )
      )
    )
    (assert (not (fp.isNaN result_rne)))
    (assert (not (fp.isNaN result_rtp)))
    (check-sat)
    (get-model)
  */
  Float64 a(1, 0b01110000000, UINT64_C(0x0111fe0000000));
  Float32 resultRNE = a.convertToFloat<8, 24>(JFS_RM_RNE);
  Float32 resultRTP = a.convertToFloat<8, 24>(JFS_RM_RTP);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTP));
  ASSERT_EQ(resultRNE, Float32(1, 0x00, UINT32_C(0b10000000100010010000000)));
  ASSERT_EQ(resultRTP, Float32(1, 0x00, UINT32_C(0b10000000100010001111111)));
}

TEST(ConvertToFloatFromFloat, Float64ToFloat32_Diff_RNE_RTN) {
  // These values are derived from a Z3 model run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (define-fun result_rne () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RNE a))
    (define-fun result_rtn () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTN a))
    (assert (not (fp.isNaN a)))
    (assert
      (not
        (fp.eq
          result_rne
          result_rtn
        )
      )
    )
    (assert (not (fp.isNaN result_rne)))
    (assert (not (fp.isNaN result_rtn)))
    (check-sat)
    (get-model)
  */
  Float64 a(1, 0b01000000000, UINT64_C(0xfff0ff8000103));
  Float32 resultRNE = a.convertToFloat<8, 24>(JFS_RM_RNE);
  Float32 resultRTN = a.convertToFloat<8, 24>(JFS_RM_RTN);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTN));
  ASSERT_EQ(resultRNE, Float32::getNegativeZero());
  ASSERT_EQ(resultRTN, Float32(1, 0x00, UINT32_C(0b00000000000000000000001)));
}

TEST(ConvertToFloatFromFloat, Float64ToFloat32_Diff_RNE_RTZ) {
  // These values are derived from a Z3 model run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (define-fun result_rne () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RNE a))
    (define-fun result_rtz () (_ FloatingPoint 8 24) ((_ to_fp 8 24) RTZ a))
    (assert (not (fp.isNaN a)))
    (assert
      (not
        (fp.eq
          result_rne
          result_rtz
        )
      )
    )
    (assert (not (fp.isNaN result_rne)))
    (assert (not (fp.isNaN result_rtz)))
    (check-sat)
    (get-model)
  */
  Float64 a(0, 0b10101111110, UINT64_C(0xffffff5004187));
  Float32 resultRNE = a.convertToFloat<8, 24>(JFS_RM_RNE);
  Float32 resultRTZ = a.convertToFloat<8, 24>(JFS_RM_RTZ);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTZ));
  ASSERT_EQ(resultRNE, Float32::getPositiveInfinity());
  ASSERT_EQ(resultRTZ, Float32(0, 0xfe, UINT32_C(0b11111111111111111111111)));
}

// FIXME: Write more tests
