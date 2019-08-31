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

TEST(Add, NaN) {
  ASSERT_TRUE(Float32::getNaN().add(JFS_RM_RNE, Float32(0.0f)).isNaN());
  ASSERT_TRUE(Float64::getNaN().add(JFS_RM_RNE, Float64(0.0)).isNaN());
}

TEST(Add, Simple) {
  ASSERT_EQ(3.0f, Float32(1.0f).add(JFS_RM_RNE, Float32(2.0f)).getRawData());
}

TEST(Add, DiffResultRNE_RTP_Float32) {
  // These values are derived from a Z3 model run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 8 24))
    (declare-fun b () (_ FloatingPoint 8 24))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert
      (not
        (fp.eq
          (fp.add RNE a b)
          (fp.add RTP a b)
        )
      )
    )
    (check-sat)
    (get-model)
  */
  Float32 a(1, 0xbc, 0b00110000000000010011111);
  Float32 b(1, 0xc3, 0b11111101101000000000000);
  Float32 addRNE = a.add(JFS_RM_RNE, b);
  Float32 addRTP = a.add(JFS_RM_RTP, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTP));
  // FIXME: Check the result values
}

TEST(Add, DiffResultRNE_RTP_Float64) {
  // These values are derived from a Z3 model run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (declare-fun b () (_ FloatingPoint 11 53))
    (define-fun a_b_rne () (_ FloatingPoint 11 53) (fp.add RNE a b))
    (define-fun a_b_rtp () (_ FloatingPoint 11 53) (fp.add RTP a b))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.eq a_b_rne a_b_rtp)))
    (assert (not (fp.isNaN a_b_rne)))
    (assert (not (fp.isNaN a_b_rtp)))
    (check-sat)
    (get-model)
  */
  Float64 a(0, 0x02, UINT64_C(0xff5edfffe64e7));
  Float64 b(0, 0x02, UINT64_C(0xff7effffe6566));
  Float64 addRNE = a.add(JFS_RM_RNE, b);
  Float64 addRTP = a.add(JFS_RM_RTP, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTP));
  // FIXME: Check the result values
}

TEST(Add, DiffResultRNE_RTN_Float32) {
  // These values are derived from a Z3 model run on the following query
  /*
    (declare-fun a () (_ FloatingPoint 8 24))
    (declare-fun b () (_ FloatingPoint 8 24))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert
      (not
        (fp.eq
          (fp.add RNE a b)
          (fp.add RTN a b)
        )
      )
    )
    (check-sat)
    (get-model)
   */
  Float32 a(0, 0x86, 0b00000000000000100100011);
  Float32 b(0, 0x85, 0b11111111111111000111101);
  Float32 addRNE = a.add(JFS_RM_RNE, b);
  Float32 addRTN = a.add(JFS_RM_RTN, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTN));
  // FIXME: Check the result values
}

TEST(Add, DiffResultRNE_RTN_Float64) {
  // These values are derived from a Z3 model run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (declare-fun b () (_ FloatingPoint 11 53))
    (define-fun a_b_rne () (_ FloatingPoint 11 53) (fp.add RNE a b))
    (define-fun a_b_rtn () (_ FloatingPoint 11 53) (fp.add RTN a b))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.eq a_b_rne a_b_rtn)))
    (assert (not (fp.isNaN a_b_rne)))
    (assert (not (fp.isNaN a_b_rtn)))
    (check-sat)
    (get-model)
  */
  Float64 a(1, 0b10000110111, UINT64_C(0xfffffffffffff));
  Float64 b(1, 0b01101111100, UINT64_C(0x9ffffffffffff));
  Float64 addRNE = a.add(JFS_RM_RNE, b);
  Float64 addRTN = a.add(JFS_RM_RTN, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTN));
  // FIXME: Check the result values
}

TEST(Add, DiffResultRNE_RTZ_Float32) {
  // These values are derived from a Z3 model run on the following query
  /*
    (declare-fun a () (_ FloatingPoint 8 24))
    (declare-fun b () (_ FloatingPoint 8 24))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert
      (not
        (fp.eq
          (fp.add RNE a b)
          (fp.add RTZ a b)
        )
      )
    )
    (check-sat)
    (get-model)
   */
  Float32 a(1, 0x3f, 0b10000001000000000011111);
  Float32 b(1, 0x3d, 0b11111111100000000000010);
  Float32 addRNE = a.add(JFS_RM_RNE, b);
  Float32 addRTZ = a.add(JFS_RM_RTZ, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTZ));
  // FIXME: Check the result values
}

TEST(Add, DiffResultRNE_RTZ_Float64) {
  // These values are derived from a Z3 model run on the following query
  /*
   *
    (declare-fun a () (_ FloatingPoint 11 53))
    (declare-fun b () (_ FloatingPoint 11 53))
    (define-fun a_b_rne () (_ FloatingPoint 11 53) (fp.add RNE a b))
    (define-fun a_b_rtz () (_ FloatingPoint 11 53) (fp.add RTZ a b))
    (assert (not (fp.isNaN a)))
    (assert (not (fp.isNaN b)))
    (assert (not (fp.eq a_b_rne a_b_rtz)))
    (assert (not (fp.isNaN a_b_rne)))
    (assert (not (fp.isNaN a_b_rtz)))
    (check-sat)
    (get-model)
  */
  Float64 a(0, 0b11100010010, UINT64_C(0xb68bfefffffe0));
  Float64 b(0, 0b11011101010, UINT64_C(0x9ffffffffffff));
  Float64 addRNE = a.add(JFS_RM_RNE, b);
  Float64 addRTZ = a.add(JFS_RM_RTZ, b);
  ASSERT_FALSE(addRNE.ieeeEquals(addRTZ));
  // FIXME: Check the result values
}
