//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "SMTLIB/NativeBitVector.h"
#include "gtest/gtest.h"
#include <memory>
#include <string.h>

TEST(WriteToBuffer, ByteAligned) {
  const jfs_nr_bitvector_ty input = 0b10110001;
  const jfs_nr_width_ty bitWidth = 8;

  const uint64_t bufferSize = 3;
  uint8_t buffer[bufferSize];
  // Initialize the buffer with surrounding data that should be preserved.
  buffer[0] = 0b00111111;
  buffer[1] = 0b10101010;
  buffer[2] = 0b11000011;

  jfs_nr_write_bitvector(input, bitWidth, buffer, bufferSize, 8);

  ASSERT_EQ(buffer[0], 0b00111111); // Unchanged
  ASSERT_EQ(buffer[1], 0b10110001);
  ASSERT_EQ(buffer[2], 0b11000011); // Unchanged

  const jfs_nr_bitvector_ty output =
      jfs_nr_make_bitvector(buffer, bufferSize, 8, 15);

  ASSERT_EQ(input, output);
}

TEST(WriteToBuffer, SplitBytes) {
  const jfs_nr_bitvector_ty input = 0b101100011011;
  const jfs_nr_width_ty bitWidth = 12;

  const uint64_t bufferSize = 3;
  uint8_t buffer[bufferSize];
  // Initialize the buffer with surrounding data that should be preserved.
  buffer[0] = 0b00111111;
  buffer[1] = 0b10101010;
  buffer[2] = 0b11000011;

  jfs_nr_write_bitvector(input, bitWidth, buffer, bufferSize, 6);

  ASSERT_EQ(buffer[0], 0b11111111);
  ASSERT_EQ(buffer[1], 0b11000110);
  ASSERT_EQ(buffer[2], 0b11000010);

  const jfs_nr_bitvector_ty output =
      jfs_nr_make_bitvector(buffer, bufferSize, 6, 17);

  ASSERT_EQ(input, output);
}

TEST(WriteToBuffer, MiddleOfBuffer) {
  const jfs_nr_bitvector_ty input = 0b101100;
  const jfs_nr_width_ty bitWidth = 6;

  const uint64_t bufferSize = 4;
  uint8_t buffer[bufferSize];
  // Initialize the buffer with surrounding data that should be preserved.
  buffer[0] = 0b00111111;
  buffer[1] = 0b10101010;
  buffer[2] = 0b11000011;
  buffer[3] = 0b11110000;

  jfs_nr_write_bitvector(input, bitWidth, buffer, bufferSize, 13);

  ASSERT_EQ(buffer[0], 0b00111111); // Unchanged
  ASSERT_EQ(buffer[1], 0b10001010);
  ASSERT_EQ(buffer[2], 0b11000101);
  ASSERT_EQ(buffer[3], 0b11110000); // Unchanged

  const jfs_nr_bitvector_ty output =
      jfs_nr_make_bitvector(buffer, bufferSize, 13, 18);

  ASSERT_EQ(input, output);
}

TEST(WriteToBuffer, SeveralVectors) {
  const jfs_nr_bitvector_ty in1 = 0b101100;
  const jfs_nr_width_ty width1 = 6;
  const jfs_nr_bitvector_ty in2 = 0b101;
  const jfs_nr_width_ty width2 = 3;
  const jfs_nr_bitvector_ty in3 = 0b1100001;
  const jfs_nr_width_ty width3 = 7;


  const uint64_t bufferSize = 3;
  uint8_t buffer[bufferSize];
  // Initialize the buffer with surrounding data that should be preserved.
  buffer[0] = 0b00111111;
  buffer[1] = 0b10101010;
  buffer[2] = 0b11000001;

  jfs_nr_write_bitvector(in1, width1, buffer, bufferSize, 2);
  jfs_nr_write_bitvector(in2, width2, buffer, bufferSize, 8);
  jfs_nr_write_bitvector(in3, width3, buffer, bufferSize, 11);


  ASSERT_EQ(buffer[0], 0b10110011);
  ASSERT_EQ(buffer[1], 0b00001101);
  ASSERT_EQ(buffer[2], 0b11000011);

  const jfs_nr_bitvector_ty out1 =
      jfs_nr_make_bitvector(buffer, bufferSize, 2, 7);
  const jfs_nr_bitvector_ty out2 =
      jfs_nr_make_bitvector(buffer, bufferSize, 8, 10);
  const jfs_nr_bitvector_ty out3 =
      jfs_nr_make_bitvector(buffer, bufferSize, 11, 17);

  ASSERT_EQ(in1, out1);
  ASSERT_EQ(in2, out2);
  ASSERT_EQ(in3, out3);
}