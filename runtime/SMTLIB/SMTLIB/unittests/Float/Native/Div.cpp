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

TEST(Div, NaN) {
  ASSERT_TRUE(Float32::getNaN().div(JFS_RM_RNE, Float32(1.0f)).isNaN());
  ASSERT_TRUE(Float64::getNaN().div(JFS_RM_RNE, Float64(1.0)).isNaN());
}

TEST(Div, DivByZero) {
  ASSERT_TRUE(
      Float32::getPositiveZero().div(JFS_RM_RNE, Float32(0.0f)).isNaN());
  ASSERT_TRUE(
      Float32::getNegativeZero().div(JFS_RM_RNE, Float32(0.0f)).isNaN());
  ASSERT_TRUE(Float64::getPositiveZero().div(JFS_RM_RNE, Float64(0.0)).isNaN());
  ASSERT_TRUE(Float64::getNegativeZero().div(JFS_RM_RNE, Float64(0.0)).isNaN());
}

TEST(Div, Simple) {
  ASSERT_EQ(4.0f, Float32(8.0f).div(JFS_RM_RNE, Float32(2.0f)).getRawData());
  ASSERT_EQ(4.0, Float64(8.0).div(JFS_RM_RNE, Float64(2.0)).getRawData());
}

TEST(Div, DiffResultRNE_RTP_Float32) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 8 24))
    (declare-fun b () (_ FloatingPoint 8 24))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert
      (not
        (fp.eq
          (fp.div RNE a b)
          (fp.div RTP a b)
        )
      )
    )
    (check-sat)
    (get-model)
  */
  Float32 a(0, 0x7f, 0b00000000000000000000000);
  Float32 b(1, 0x7e, 0b11111111111000000000000);
  Float32 addRNE = a.div(JFS_RM_RNE, b);
  Float32 addRTP = a.div(JFS_RM_RTP, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTP));
  // FIXME: Check the result values
}

TEST(Div, DiffResultRNE_RTP_Float64) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (declare-fun b () (_ FloatingPoint 11 53))
    (define-fun a_b_rne () (_ FloatingPoint 11 53) (fp.div RNE a b))
    (define-fun a_b_rtp () (_ FloatingPoint 11 53) (fp.div RTP a b))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.eq a_b_rne a_b_rtp)))
    (assert (not (fp.isNaN a_b_rne)))
    (assert (not (fp.isNaN a_b_rtp)))
    (check-sat)
    (get-model)
  */
  Float64 a(0, 0b00000000000, UINT64_C(0x410815d750e65));
  Float64 b(0, 0b10000011011, UINT64_C(0x021c1b000e7c0));
  Float64 addRNE = a.div(JFS_RM_RNE, b);
  Float64 addRTP = a.div(JFS_RM_RTP, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTP));
  // FIXME: Check the result values
}

TEST(Div, DiffResultRNE_RTN_Float32) {
  // These values are derived from Z3 being run on the following query
  /*
    (declare-fun a () (_ FloatingPoint 8 24))
    (declare-fun b () (_ FloatingPoint 8 24))
    (define-fun a_b_rne () (_ FloatingPoint 8 24) (fp.div RNE a b))
    (define-fun a_b_rtn () (_ FloatingPoint 8 24) (fp.div RTN a b))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert
      (not
        (fp.eq
          a_b_rne
          a_b_rtn
        )
      )
    )
    (assert (not (fp.isNaN a_b_rne)))
    (assert (not (fp.isNaN a_b_rtn)))
    (check-sat)
    (get-model)
   */
  Float32 a(0, 0x3e, 0b10010010000011110111111);
  Float32 b(1, 0xd9, 0b10001101110101011000000);
  Float32 addRNE = a.div(JFS_RM_RNE, b);
  Float32 addRTN = a.div(JFS_RM_RTN, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTN));
  // FIXME: Check the result values
}

TEST(Div, DiffResultRNE_RTN_Float64) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (declare-fun b () (_ FloatingPoint 11 53))
    (define-fun a_b_rne () (_ FloatingPoint 11 53) (fp.div RNE a b))
    (define-fun a_b_rtn () (_ FloatingPoint 11 53) (fp.div RTN a b))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.eq a_b_rne a_b_rtn)))
    (assert (not (fp.isNaN a_b_rne)))
    (assert (not (fp.isNaN a_b_rtn)))
    (check-sat)
    (get-model)
  */
  Float64 a(1, 0b00000000000, UINT64_C(0x410815d750e65));
  Float64 b(0, 0b10000011011, UINT64_C(0x021c1b000e7c0));
  Float64 addRNE = a.div(JFS_RM_RNE, b);
  Float64 addRTN = a.div(JFS_RM_RTN, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTN));
  // FIXME: Check the result values
}

TEST(Div, DiffResultRNE_RTZ_Float32) {
  // These values are derived from Z3 being run on the following query
  /*
    (declare-fun a () (_ FloatingPoint 8 24))
    (declare-fun b () (_ FloatingPoint 8 24))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert
      (not
        (fp.eq
          (fp.div RNE a b)
          (fp.div RTZ a b)
        )
      )
    )
    (check-sat)
    (get-model)
   */
  Float32 a(1, 0x00, UINT32_C(0b01000010010001100110011));
  Float32 b(1, 0x7f, UINT32_C(0b00010000000000000110001));
  Float32 addRNE = a.div(JFS_RM_RNE, b);
  Float32 addRTZ = a.div(JFS_RM_RTZ, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTZ));
  // FIXME: Check the result values
}

TEST(Div, DiffResultRNE_RTZ_Float64) {
  // These values are derived from Z3 being run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (declare-fun b () (_ FloatingPoint 11 53))
    (define-fun a_b_rne () (_ FloatingPoint 11 53) (fp.div RNE a b))
    (define-fun a_b_rtz () (_ FloatingPoint 11 53) (fp.div RTZ a b))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.eq a_b_rne a_b_rtz)))
    (assert (not (fp.isNaN a_b_rne)))
    (assert (not (fp.isNaN a_b_rtz)))
    (check-sat)
    (get-model)
  */
  Float64 a(1, 0b00101111110, UINT64_C(0xcfb924e8e8e89));
  Float64 b(1, 0b10101111101, UINT64_C(0x0cb1d4012c003));
  Float64 addRNE = a.div(JFS_RM_RNE, b);
  Float64 addRTZ = a.div(JFS_RM_RTZ, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTZ));
  // FIXME: Check the result values
}
