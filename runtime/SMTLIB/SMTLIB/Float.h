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
  Float(const BitVector<32> bits)
      : data(jfs_nr_bitcast_bv_to_float32(bits.data)) {}

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

  bool ieeeEquals(const Float32& other) const {
    return jfs_nr_float32_ieee_equals(data, other.data);
  }

  bool fplt(const Float32& other) const {
    return jfs_nr_float32_lt(data, other.data);
  }
  bool fpleq(const Float32& other) const {
    return jfs_nr_float32_leq(data, other.data);
  }
  bool fpgt(const Float32& other) const {
    return jfs_nr_float32_gt(data, other.data);
  }
  bool fpgeq(const Float32& other) const {
    return jfs_nr_float32_geq(data, other.data);
  }

  // Arithmetic
  Float32 abs() const { return jfs_nr_float32_abs(data); }
  Float32 neg() const { return jfs_nr_float32_neg(data); }
  Float32 add(JFS_NR_RM rm, const Float32& other) const {
    return jfs_nr_float32_add(rm, data, other.data);
  };
  Float32 sub(JFS_NR_RM rm, const Float32& other) const {
    return jfs_nr_float32_sub(rm, data, other.data);
  };
  Float32 mul(JFS_NR_RM rm, const Float32& other) const {
    return jfs_nr_float32_mul(rm, data, other.data);
  };
  Float32 div(JFS_NR_RM rm, const Float32& other) const {
    return jfs_nr_float32_div(rm, data, other.data);
  };
  Float32 fma(JFS_NR_RM rm, const Float32& b, const Float32& c) const {
    return jfs_nr_float32_fma(rm, data, b.data, c.data);
  };
  Float32 sqrt(JFS_NR_RM rm) const { return jfs_nr_float32_sqrt(rm, data); }
  Float32 rem(const Float32& other) const {
    return jfs_nr_float32_rem(data, other.data);
  };
  Float32 roundToIntegral(JFS_NR_RM rm) const {
    return jfs_nr_float32_round_to_integral(rm, data);
  }
  Float32 min(const Float32& other) const {
    return jfs_nr_float32_min(data, other.data);
  }
  Float32 max(const Float32& other) const {
    return jfs_nr_float32_max(data, other.data);
  }

  // Prediactes
  bool isNormal() const { return jfs_nr_float32_is_normal(data); }
  bool isSubnormal() const { return jfs_nr_float32_is_subnormal(data); }
  bool isZero() const { return jfs_nr_float32_is_zero(data); }
  bool isInfinite() const { return jfs_nr_float32_is_infinite(data); }
  bool isPositive() const { return jfs_nr_float32_is_positive(data); }
  bool isNegative() const { return jfs_nr_float32_is_negative(data); }
  bool isNaN() const { return jfs_nr_float32_is_nan(data); }

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
  Float(const BitVector<64> bits)
      : data(jfs_nr_bitcast_bv_to_float64(bits.data)) {}

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

  bool ieeeEquals(const Float64& other) const {
    return jfs_nr_float64_ieee_equals(data, other.data);
  }

  bool fplt(const Float64& other) const {
    return jfs_nr_float64_lt(data, other.data);
  }
  bool fpleq(const Float64& other) const {
    return jfs_nr_float64_leq(data, other.data);
  }
  bool fpgt(const Float64& other) const {
    return jfs_nr_float64_gt(data, other.data);
  }
  bool fpgeq(const Float64& other) const {
    return jfs_nr_float64_geq(data, other.data);
  }

  // Arithmetic
  Float64 abs() const { return jfs_nr_float64_abs(data); }
  Float64 neg() const { return jfs_nr_float64_neg(data); }
  Float64 add(JFS_NR_RM rm, const Float64& other) const {
    return jfs_nr_float64_add(rm, data, other.data);
  };
  Float64 sub(JFS_NR_RM rm, const Float64& other) const {
    return jfs_nr_float64_sub(rm, data, other.data);
  };
  Float64 mul(JFS_NR_RM rm, const Float64& other) const {
    return jfs_nr_float64_mul(rm, data, other.data);
  };
  Float64 div(JFS_NR_RM rm, const Float64& other) const {
    return jfs_nr_float64_div(rm, data, other.data);
  };
  Float64 fma(JFS_NR_RM rm, const Float64& b, const Float64& c) const {
    return jfs_nr_float64_fma(rm, data, b.data, c.data);
  };
  Float64 sqrt(JFS_NR_RM rm) const { return jfs_nr_float64_sqrt(rm, data); }
  Float64 rem(const Float64& other) const {
    return jfs_nr_float64_rem(data, other.data);
  };
  Float64 roundToIntegral(JFS_NR_RM rm) const {
    return jfs_nr_float64_round_to_integral(rm, data);
  }
  Float64 min(const Float64& other) const {
    return jfs_nr_float64_min(data, other.data);
  }
  Float64 max(const Float64& other) const {
    return jfs_nr_float64_max(data, other.data);
  }

  // Predicates
  bool isNormal() const { return jfs_nr_float64_is_normal(data); }
  bool isSubnormal() const { return jfs_nr_float64_is_subnormal(data); }
  bool isZero() const { return jfs_nr_float64_is_zero(data); }
  bool isInfinite() const { return jfs_nr_float64_is_infinite(data); }
  bool isPositive() const { return jfs_nr_float64_is_positive(data); }
  bool isNegative() const { return jfs_nr_float64_is_negative(data); }
  bool isNaN() const { return jfs_nr_float64_is_nan(data); }

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
