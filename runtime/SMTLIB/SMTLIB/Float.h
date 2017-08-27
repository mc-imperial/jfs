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
#ifndef JFS_RUNTIME_SMTLIB_FLOAT_H
#define JFS_RUNTIME_SMTLIB_FLOAT_H
#include "BitVector.h"
#include "BufferRef.h"
#include "NativeFloat.h"
#include <stdint.h>

// Arbitary precision floating point with
// EB exponent bits and SB significand bits (includes implicit bit)
// that mimics the semantics of SMT-LIBv2
// TODO: Implement genric version
template <uint64_t EB, uint64_t SB> class Float {};

typedef Float<8, 24> Float32;
typedef Float<11, 53> Float64;

// FIXME: Refactor this so we don't duplicate code
// Specialize for native types
template <> class Float<8, 24> {
private:
  jfs_nr_float32 data;

public:
  Float(jfs_nr_float32 value) : data(value) {}
  Float() : data(0.0f) {}
  Float(const Float<8, 24>& other) { data = other.data; }
  Float(BitVector<1> sign, BitVector<8> exponent, BitVector<23> significand) {
    data = jfs_nr_make_float32_from_triple(sign.data, exponent.data,
                                           significand.data);
  }

  // Special constants
  static Float32 getPositiveInfinity() {
    return jfs_nr_float32_get_infinity(true);
  }
  static Float32 getNegativeInfinity() {
    return jfs_nr_float32_get_infinity(false);
  }
  static Float32 getPositiveZero() { return jfs_nr_float32_get_zero(true); }
  static Float32 getNegativeZero() { return jfs_nr_float32_get_zero(false); }
  static Float32 getNaN() { return jfs_nr_float32_get_nan(true); }

  // SMT-LIBv2 bit comparison
  bool operator==(const Float32& other) const {
    return jfs_nr_float32_smtlib_equals(data, other.data);
  }
  // For testing
  uint32_t getRawBits() const { return jfs_nr_float32_get_raw_bits(data); }
  jfs_nr_float32 getRawData() const { return data; }
};

template <> class Float<11, 53> {
private:
  jfs_nr_float64 data;

public:
  Float(jfs_nr_float64 value) : data(value) {}
  Float() : data(0.0) {}
  Float(const Float<11, 53>& other) { data = other.data; }
  Float(BitVector<1> sign, BitVector<11> exponent, BitVector<52> significand) {
    data = jfs_nr_make_float64_from_triple(sign.data, exponent.data,
                                           significand.data);
  }

  // Special constants
  static Float64 getPositiveInfinity() {
    return jfs_nr_float64_get_infinity(true);
  }
  static Float64 getNegativeInfinity() {
    return jfs_nr_float64_get_infinity(false);
  }
  static Float64 getPositiveZero() { return jfs_nr_float64_get_zero(true); }
  static Float64 getNegativeZero() { return jfs_nr_float64_get_zero(false); }
  static Float64 getNaN() { return jfs_nr_float64_get_nan(true); }

  // SMT-LIBv2 bit comparison
  bool operator==(const Float64& other) const {
    return jfs_nr_float64_smtlib_equals(data, other.data);
  }
  // For testing
  uint64_t getRawBits() const { return jfs_nr_float64_get_raw_bits(data); }
  jfs_nr_float64 getRawData() const { return data; }
};

template <uint64_t EB, uint64_t SB>
Float<EB, SB> makeFloatFrom(BufferRef<const uint8_t> buffer, uint64_t lowBit,
                            uint64_t highBit);

// Specialize for Float32
template <>
Float32 makeFloatFrom(BufferRef<const uint8_t> buffer, uint64_t lowBit,
                      uint64_t highBit);

// Specialize for Float64
template <>
Float64 makeFloatFrom(BufferRef<const uint8_t> buffer, uint64_t lowBit,
                      uint64_t highBit);
#endif
