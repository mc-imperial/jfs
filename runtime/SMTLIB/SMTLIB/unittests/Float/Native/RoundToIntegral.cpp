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

TEST(RoundToIntegral, NaN) {
  ASSERT_TRUE(Float32::getNaN().roundToIntegral(JFS_RM_RNE).isNaN());
  ASSERT_TRUE(Float64::getNaN().roundToIntegral(JFS_RM_RNE).isNaN());
}

TEST(RoundToIntegral, SimpleFloat32) {
  ASSERT_EQ(0.0f, Float32(-0.1f).roundToIntegral(JFS_RM_RNE).getRawData());
  ASSERT_EQ(0.0f, Float32(-0.1f).roundToIntegral(JFS_RM_RTP).getRawData());
  ASSERT_EQ(-1.0f, Float32(-0.1f).roundToIntegral(JFS_RM_RTN).getRawData());
  ASSERT_EQ(0.0f, Float32(-0.1f).roundToIntegral(JFS_RM_RTZ).getRawData());
}

TEST(RoundToIntegral, SimpleFloat64) {
  ASSERT_EQ(0.0, Float64(-0.1).roundToIntegral(JFS_RM_RNE).getRawData());
  ASSERT_EQ(0.0, Float64(-0.1).roundToIntegral(JFS_RM_RTP).getRawData());
  ASSERT_EQ(-1.0, Float64(-0.1).roundToIntegral(JFS_RM_RTN).getRawData());
  ASSERT_EQ(0.0, Float64(-0.1).roundToIntegral(JFS_RM_RTZ).getRawData());
}

// FIXME: Write more tests
