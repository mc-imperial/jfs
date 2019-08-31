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

TEST(Sqrt, NaN) {
  ASSERT_TRUE(Float32::getNaN().sqrt(JFS_RM_RNE).isNaN());
  ASSERT_TRUE(Float64::getNaN().sqrt(JFS_RM_RNE).isNaN());
}

TEST(Sqrt, Simple) {
  ASSERT_EQ(2.0f, Float32(4.0f).sqrt(JFS_RM_RNE).getRawData());
  ASSERT_EQ(2.0, Float64(4.0).sqrt(JFS_RM_RNE).getRawData());
}

TEST(Sqrt, DiffResultRNE_RTP_Float32) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 8 24))
    (define-fun result_rne () (_ FloatingPoint 8 24) (fp.sqrt RNE a))
    (define-fun result_rtp () (_ FloatingPoint 8 24) (fp.sqrt RTP a))
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
    (get-value (result_rne))
    (get-value (result_rtp))
  */
  Float32 a(0, 0xf5, UINT32_C(0b10000011011110111001001));
  Float32 resultRNE = a.sqrt(JFS_RM_RNE);
  Float32 resultRTP = a.sqrt(JFS_RM_RTP);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTP));
  ASSERT_EQ(resultRNE, Float32(0, 0xba, UINT32_C(0b00111010111101000000101)));
  ASSERT_EQ(resultRTP, Float32(0, 0xba, UINT32_C(0b00111010111101000000110)));
}

TEST(Sqrt, DiffResultRNE_RTP_Float64) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (define-fun result_rne () (_ FloatingPoint 11 53) (fp.sqrt RNE a))
    (define-fun result_rtp () (_ FloatingPoint 11 53) (fp.sqrt RTP a))
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
    (get-value (result_rne))
    (get-value (result_rtp))
  */
  Float64 a(0, 0b00000000100, UINT64_C(0x26a5a80660dbe));
  Float64 resultRNE = a.sqrt(JFS_RM_RNE);
  Float64 resultRTP = a.sqrt(JFS_RM_RTP);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTP));
  ASSERT_EQ(resultRNE, Float64(0, 0b01000000001, UINT64_C(0x8467f75d9d7b2)));
  ASSERT_EQ(resultRTP, Float64(0, 0b01000000001, UINT64_C(0x8467f75d9d7b3)));
}

// FIXME: Write tests for other rounding modes and types
