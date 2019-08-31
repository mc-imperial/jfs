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

TEST(FMA, NaN) {
  ASSERT_TRUE(
      Float32::getNaN().fma(JFS_RM_RNE, Float32(1.0f), Float32(1.0f)).isNaN());
  ASSERT_TRUE(
      Float64::getNaN().fma(JFS_RM_RNE, Float64(1.0f), Float64(1.0f)).isNaN());
}

TEST(FMA, Simple) {
  ASSERT_EQ(
      7.0f,
      Float32(2.0f).fma(JFS_RM_RNE, Float32(3.0f), Float32(1.0f)).getRawData());
  ASSERT_EQ(
      7.0,
      Float64(2.0).fma(JFS_RM_RNE, Float64(3.0), Float64(1.0)).getRawData());
}

TEST(FMA, DiffResultRNE_RTP_Float32) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 8 24))
    (declare-fun b () (_ FloatingPoint 8 24))
    (declare-fun c () (_ FloatingPoint 8 24))
    (define-fun result_rne () (_ FloatingPoint 8 24) (fp.fma RNE a b c))
    (define-fun result_rtp () (_ FloatingPoint 8 24) (fp.fma RTP a b c))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.isNaN c)))
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
  Float32 a(0, 0x7e, 0b00000111111111010000000);
  Float32 b(0, 0x00, 0b00000000000000001111101);
  Float32 c(1, 0x98, 0b00000000000100011000000);
  Float32 resultRNE = a.fma(JFS_RM_RNE, b, c);
  Float32 resultRTP = a.fma(JFS_RM_RTP, b, c);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTP));
  // FIXME: Check the result values
}

TEST(FMA, DiffResultRNE_RTP_Float64) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (declare-fun b () (_ FloatingPoint 11 53))
    (declare-fun c () (_ FloatingPoint 11 53))
    (define-fun result_rne () (_ FloatingPoint 11 53) (fp.fma RNE a b c))
    (define-fun result_rtp () (_ FloatingPoint 11 53) (fp.fma RTP a b c))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.isNaN c)))
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
  Float64 a(1, 0b11111111101, UINT64_C(0x036919b77c30c));
  Float64 b(0, 0b11111111100, UINT64_C(0x10000005b5620));
  Float64 c(0, 0b01110011111, UINT64_C(0x0000000000000));
  Float64 resultRNE = a.fma(JFS_RM_RNE, b, c);
  Float64 resultRTP = a.fma(JFS_RM_RTP, b, c);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTP));
  // FIXME: Check the result values
}

TEST(FMA, DiffResultRNE_RTN_Float32) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 8 24))
    (declare-fun b () (_ FloatingPoint 8 24))
    (declare-fun c () (_ FloatingPoint 8 24))
    (define-fun result_rne () (_ FloatingPoint 8 24) (fp.fma RNE a b c))
    (define-fun result_rtn () (_ FloatingPoint 8 24) (fp.fma RTN a b c))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.isNaN c)))
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
  Float32 a(0, 0xfe, 0b11111011110001000001110);
  Float32 b(0, 0x05, 0b00000000000000000000000);
  Float32 c(0, 0x80, 0b01111000000101111111111);
  Float32 resultRNE = a.fma(JFS_RM_RNE, b, c);
  Float32 resultRTN = a.fma(JFS_RM_RTN, b, c);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTN));
  // FIXME: Check the result values
}

TEST(FMA, DiffResultRNE_RTN_Float64) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (declare-fun b () (_ FloatingPoint 11 53))
    (declare-fun c () (_ FloatingPoint 11 53))
    (define-fun result_rne () (_ FloatingPoint 11 53) (fp.fma RNE a b c))
    (define-fun result_rtn () (_ FloatingPoint 11 53) (fp.fma RTN a b c))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.isNaN c)))
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
  Float64 a(0, 0b00000000000, UINT64_C(0x8204000000010));
  Float64 b(1, 0b11111111110, UINT64_C(0x0000000010000));
  Float64 c(0, 0b10001111111, UINT64_C(0x0000000000000));
  Float64 resultRNE = a.fma(JFS_RM_RNE, b, c);
  Float64 resultRTN = a.fma(JFS_RM_RTN, b, c);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTN));
  // FIXME: Check the result values
}

TEST(FMA, DiffResultRNE_RTZ_Float32) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 8 24))
    (declare-fun b () (_ FloatingPoint 8 24))
    (declare-fun c () (_ FloatingPoint 8 24))
    (define-fun result_rne () (_ FloatingPoint 8 24) (fp.fma RNE a b c))
    (define-fun result_rtz () (_ FloatingPoint 8 24) (fp.fma RTZ a b c))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.isNaN c)))
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
  Float32 a(1, 0x00, UINT32_C(0b00000000000000100100000));
  Float32 b(1, 0x88, UINT32_C(0b01101010001110001110000));
  Float32 c(0, 0x07, UINT32_C(0b00000001100010101000101));
  Float32 resultRNE = a.fma(JFS_RM_RNE, b, c);
  Float32 resultRTZ = a.fma(JFS_RM_RTZ, b, c);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTZ));
  // FIXME: Check the result values
}

TEST(FMA, DiffResultRNE_RTZ_Float64) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (declare-fun b () (_ FloatingPoint 11 53))
    (declare-fun c () (_ FloatingPoint 11 53))
    (define-fun result_rne () (_ FloatingPoint 11 53) (fp.fma RNE a b c))
    (define-fun result_rtz () (_ FloatingPoint 11 53) (fp.fma RTZ a b c))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.isNaN c)))
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
  Float64 a(1, 0b00101000000, UINT64_C(0xf723129ff9530));
  Float64 b(0, 0b11110111111, UINT64_C(0x3f670f9f1dff0));
  Float64 c(0, 0b10011111111, UINT64_C(0xf4cfc0fdffbb7));
  Float64 resultRNE = a.fma(JFS_RM_RNE, b, c);
  Float64 resultRTZ = a.fma(JFS_RM_RTZ, b, c);
  ASSERT_FALSE(resultRNE.ieeeEquals(resultRTZ));
  ASSERT_EQ(resultRNE, Float64(1, 0b10100000000, UINT64_C(0x795761869e022)));
  ASSERT_EQ(resultRTZ, Float64(1, 0b10100000000, UINT64_C(0x795761869e021)));
}
