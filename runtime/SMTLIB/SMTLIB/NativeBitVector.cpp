//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
// This is the implemenation of the runtime for SMTLIB BitVectors that
// uses native machine operations. It is written with a C compatible interface
// so that in the future we can easily use LLVM's JIT.

#include "SMTLIB/NativeBitVector.h"

// Helper constants/functions
namespace {

const jfs_nr_width_ty jfs_nr_bitvector_ty_bit_width =
    sizeof(jfs_nr_bitvector_ty) * 8;

jfs_nr_bitvector_ty jfs_nr_get_bitvector_mask(const jfs_nr_width_ty bitWidth) {
  static_assert(jfs_nr_bitvector_ty_bit_width <= 64, "Wrong width");
  jassert(bitWidth <= jfs_nr_bitvector_ty_bit_width);
  return (bitWidth >= jfs_nr_bitvector_ty_bit_width)
             ? UINT64_MAX
             : ((UINT64_C(1) << bitWidth) - 1);
}

jfs_nr_bitvector_ty jfs_nr_get_bitvector_mod(const jfs_nr_bitvector_ty value,
                                             const jfs_nr_width_ty bitWidth) {
  static_assert(jfs_nr_bitvector_ty_bit_width <= 64, "Wrong width");
  if (bitWidth >= jfs_nr_bitvector_ty_bit_width) {
    return value;
  } else {
    return value % (UINT64_C(1) << bitWidth);
  }
}

bool jfs_nr_is_valid(const jfs_nr_bitvector_ty value,
                     const jfs_nr_width_ty width) {
  return jfs_nr_get_bitvector_mod(value, width) == value;
}
}

#ifdef __cplusplus
extern "C" {
#endif

// Public functions

jfs_nr_bitvector_ty jfs_nr_concat(const jfs_nr_bitvector_ty lhs,
                                  const jfs_nr_width_ty lhsBitWidth,
                                  const jfs_nr_bitvector_ty rhs,
                                  const jfs_nr_width_ty rhsBitWidth) {
  jassert(jfs_nr_is_valid(lhs, lhsBitWidth));
  jassert(jfs_nr_is_valid(rhs, rhsBitWidth));
  jassert(((lhsBitWidth + rhsBitWidth) <= jfs_nr_bitvector_ty_bit_width) &&
          "concat too wide");
  jfs_nr_bitvector_ty newValue = rhs;
  newValue |= (lhs << rhsBitWidth);
  return newValue;
}

// Extract bits [highBit, lowBit]
jfs_nr_bitvector_ty jfs_nr_extract(const jfs_nr_bitvector_ty value,
                                   const jfs_nr_width_ty bitWidth,
                                   const jfs_nr_width_ty highBit,
                                   const jfs_nr_width_ty lowBit) {
  jassert(jfs_nr_is_valid(value, bitWidth));
  jassert(highBit >= lowBit && "Invalid highBit and/or lowBit value");
  jassert(highBit < bitWidth && "Invalid highBit bit");
  jassert(lowBit < bitWidth && "Invalid lowBit bit");
  const jfs_nr_width_ty newWidth = (highBit - lowBit) + 1;
  if (newWidth == bitWidth)
    return value;
  jfs_nr_bitvector_ty temp = value;
  // Remove higher bits that we don't want
  jfs_nr_bitvector_ty mask = jfs_nr_get_bitvector_mask(highBit + 1);
  temp &= mask;

  // Remove lower bits that we don't want.
  temp >>= lowBit;
  jassert(jfs_nr_is_valid(temp, newWidth));
  return temp;
}

// Convenience function for creating a BitVector
// from any arbitrary bit offset in a buffer. Offset
// is [lowbit, highbit].
jfs_nr_bitvector_ty jfs_nr_make_bitvector(const uint8_t* bufferData,
                                          const uint64_t bufferSize,
                                          const uint64_t lowBit,
                                          const uint64_t highBit) {
  jassert(highBit >= lowBit && "invalid lowBit and highBit");
  jassert(highBit < (bufferSize * 8));
  const uint64_t bitWidth = ((highBit - lowBit) + 1);
  const size_t lowBitByte = lowBit / 8;
  const size_t shiftOffset = lowBit % 8;
  // NOTE: doing `highBit / 8` to compute `highBitByte` is wrong. For [1,8]
  // that gives a highBit of 1 which is wrong for the loop below (should be 0).
  // const size_t highBitByte = (lowBitByte + ((BITWIDTH + 7) / 8)) - 1;
  const size_t highBitByte = (lowBitByte + (((highBit - lowBit) + 8) / 8)) - 1;
  jassert(lowBitByte < bufferSize);
  jassert(highBitByte < bufferSize);
  jfs_nr_bitvector_ty data = 0;
  uint8_t* dataView = reinterpret_cast<uint8_t*>(&data);
  jfs_nr_bitvector_ty dataMask = jfs_nr_get_bitvector_mask(bitWidth);
  // Copy byte-by-byte shifting if necessary
  for (size_t index = lowBitByte; index <= highBitByte; ++index) {
    const size_t viewIndex = index - lowBitByte;
    jassert(index < bufferSize);
    jassert(viewIndex < sizeof(data));
    uint8_t bufferByte = bufferData[index];
    dataView[viewIndex] |= (bufferByte >> shiftOffset);
    if (shiftOffset == 0) {
      // If there is no shift offset then we didn't shift any bits
      // out.
      continue;
    }
    // Doing the shift means we have zero bits in MSB rather than the actually
    // bits we want.
    uint8_t nextIterByteValue = 0;
    if ((index + 1) < bufferSize) {
      // Avoid out of bounds access
      nextIterByteValue = bufferData[index + 1];
    }
    dataView[viewIndex] |= (nextIterByteValue << (8 - shiftOffset));
  }
  // Now mask off the data
  data &= dataMask;
  return data;
}

#ifdef __cplusplus
}
#endif
