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
// This is the implemenation of the runtime for SMTLIB Floats that
// uses native machine operations. It is written with a C compatible interface
// so that in the future we can easily use LLVM's JIT.
#include "SMTLIB/NativeFloat.h"
#include "SMTLIB/NativeBitVector.h"
#include "SMTLIB/jassert.h"
#include <math.h>
#include <string.h>

namespace {

// Generic version
template <typename T>
T jfs_nr_internal_make_float_from_buffer(const uint8_t* bufferData,
                                         const uint64_t bufferSize,
                                         const uint64_t lowBit) {
  // Just re-use bitvector method for now.
  // This assume little-endian which might things on other architectures.
  uint64_t highBit = lowBit + (sizeof(T) * 8) - 1;
  jassert((((highBit - lowBit) + 1) % 8) == 0 &&
          "Width requested should be whole bytes");
  jfs_nr_bitvector_ty rawBits =
      jfs_nr_make_bitvector(bufferData, bufferSize, lowBit, highBit);
  T result;
  // Copy into result
  memcpy(&result, &rawBits, sizeof(T));
  return result;
}

// Generic version
template <typename RetTy, typename ArgTy>
RetTy jfs_nr_internal_float_get_raw_bits(const ArgTy value) {
  static_assert(sizeof(RetTy) == sizeof(ArgTy), "Size mismatch");
  RetTy data = 0;
  memcpy(&data, &value, sizeof(RetTy));
  return data;
}
}

#ifdef __cplusplus
extern "C" {
#endif

uint32_t jfs_nr_float32_get_raw_bits(const jfs_nr_float32 value) {
  return jfs_nr_internal_float_get_raw_bits<uint32_t, jfs_nr_float32>(value);
}

uint64_t jfs_nr_float64_get_raw_bits(const jfs_nr_float64 value) {
  return jfs_nr_internal_float_get_raw_bits<uint64_t, jfs_nr_float64>(value);
}

jfs_nr_float32 jfs_nr_float32_get_infinity(bool positive) {
  if (positive)
    return INFINITY;
  return -INFINITY;
}

jfs_nr_float64 jfs_nr_float64_get_infinity(bool positive) {
  if (positive)
    return INFINITY;
  return -INFINITY;
}

jfs_nr_float32 jfs_nr_float32_get_zero(bool positive) {
  if (positive)
    return jfs_nr_bitcast_bv_to_float32(0x0);
  return jfs_nr_bitcast_bv_to_float32(UINT32_C(0x80000000));
}

jfs_nr_float64 jfs_nr_float64_get_zero(bool positive) {
  if (positive)
    return jfs_nr_bitcast_bv_to_float64(0x0);
  return jfs_nr_bitcast_bv_to_float64(UINT64_C(0x8000000000000000));
}

jfs_nr_float32 jfs_nr_float32_get_nan(bool quiet) {
  if (quiet)
    return jfs_nr_bitcast_bv_to_float32(UINT64_C(0x7fc00000));
  return jfs_nr_bitcast_bv_to_float32(UINT64_C(0x7f800001));
}

jfs_nr_float64 jfs_nr_float64_get_nan(bool quiet) {
  if (quiet)
    return jfs_nr_bitcast_bv_to_float64(UINT64_C(0x7ff8000000000000));
  return jfs_nr_bitcast_bv_to_float64(UINT64_C(0x7ff0000000000001));
}

bool jfs_nr_float32_is_normal(const jfs_nr_float32 value) {
  return isnormal(value) != 0;
}
bool jfs_nr_float64_is_normal(const jfs_nr_float64 value) {
  return isnormal(value) != 0;
}

bool jfs_nr_float32_is_subnormal(const jfs_nr_float32 value) {
  return fpclassify(value) == FP_SUBNORMAL;
}

bool jfs_nr_float64_is_subnormal(const jfs_nr_float64 value) {
  return fpclassify(value) == FP_SUBNORMAL;
}

bool jfs_nr_float32_is_nan(const jfs_nr_float32 value) { return isnanf(value); }

bool jfs_nr_float64_is_nan(const jfs_nr_float64 value) { return isnan(value); }

bool jfs_nr_float32_smtlib_equals(const jfs_nr_float32 lhs,
                                  const jfs_nr_float32 rhs) {
  // In SMT-LIBv2 no distinction is made between the different types of NaN
  /*
   *  (set-logic QF_FPBV)
      (declare-const x (_ BitVec 32))
      (declare-const y (_ BitVec 32))
      (assert (not (= x y)))
      (assert (fp.isNaN ((_ to_fp 8 24) x)))
      (assert (fp.isNaN ((_ to_fp 8 24) y)))
      (assert
        (not
          (=
            ((_ to_fp 8 24) x)
            ((_ to_fp 8 24) y)
          )
        )
      )
      (check-sat)
      unsat
  */
  bool lhsIsNaN = isnanf(lhs);
  bool rhsIsNaN = isnanf(rhs);
  if (lhsIsNaN && rhsIsNaN) {
    return true;
  }
  // Positive and negative 0 are distinct but C's `==` operator considers them
  // equal so just do bit comparison.
  return jfs_nr_float32_get_raw_bits(lhs) == jfs_nr_float32_get_raw_bits(rhs);
}

bool jfs_nr_float64_smtlib_equals(const jfs_nr_float64 lhs,
                                  const jfs_nr_float64 rhs) {
  // In SMT-LIBv2 no distinction is made between the different types of NaN
  bool lhsIsNaN = isnan(lhs);
  bool rhsIsNaN = isnan(rhs);
  if (lhsIsNaN && rhsIsNaN) {
    return true;
  }
  // Positive and negative 0 are distinct but C's `==` operator considers them
  // equal so just do bit comparison.
  return jfs_nr_float64_get_raw_bits(lhs) == jfs_nr_float64_get_raw_bits(rhs);
}

jfs_nr_float32 jfs_nr_bitcast_bv_to_float32(const jfs_nr_bitvector_ty value) {
  jassert((value & UINT64_C(0xffffffff00000000)) == 0);
  jfs_nr_float32 data = 0.0;
  memcpy(&data, &value, sizeof(data));
  return data;
}

jfs_nr_float64 jfs_nr_bitcast_bv_to_float64(const jfs_nr_bitvector_ty value) {
  jfs_nr_float64 data = 0.0;
  memcpy(&data, &value, sizeof(data));
  return data;
}

// Note significand does not contain implicit bit
jfs_nr_float32
jfs_nr_make_float32_from_triple(const jfs_nr_bitvector_ty sign,
                                const jfs_nr_bitvector_ty exponent,
                                const jfs_nr_bitvector_ty significand) {
  static_assert((sizeof(jfs_nr_bitvector_ty) * 8) >= 32, "not enough bits");
  jassert((sign & (~(UINT64_C(0x1)))) == 0);             // only 1 bit
  jassert((exponent & (~(UINT64_C(0xff)))) == 0);        // only 8-bits
  jassert((significand & (~(UINT64_C(0x7fffff)))) == 0); // only 23-bits
  jfs_nr_bitvector_ty rawBits = significand;
  rawBits |= (exponent << 23);
  rawBits |= (sign << 31);
  return jfs_nr_bitcast_bv_to_float32(rawBits);
}

jfs_nr_float64
jfs_nr_make_float64_from_triple(const jfs_nr_bitvector_ty sign,
                                const jfs_nr_bitvector_ty exponent,
                                const jfs_nr_bitvector_ty significand) {
  // TODO: Finish!
  static_assert((sizeof(jfs_nr_bitvector_ty) * 8) >= 64, "not enough bits");
  jassert((sign & (~(UINT64_C(0x1)))) == 0);       // only 1 bit
  jassert((exponent & (~(UINT64_C(0x7ff)))) == 0); // only 11-bits
  jassert((significand & (~(UINT64_C(0x000fffffffffffff)))) ==
          0); // only 52-bits
  jfs_nr_bitvector_ty rawBits = significand;
  rawBits |= (exponent << 52);
  rawBits |= (sign << 63);
  return jfs_nr_bitcast_bv_to_float64(rawBits);
}

jfs_nr_float32 jfs_nr_make_float32_from_buffer(const uint8_t* bufferData,
                                               const uint64_t bufferSize,
                                               const uint64_t lowBit) {
  return jfs_nr_internal_make_float_from_buffer<jfs_nr_float32>(
      bufferData, bufferSize, lowBit);
}

jfs_nr_float64 jfs_nr_make_float64_from_buffer(const uint8_t* bufferData,
                                               const uint64_t bufferSize,
                                               const uint64_t lowBit) {
  return jfs_nr_internal_make_float_from_buffer<jfs_nr_float64>(
      bufferData, bufferSize, lowBit);
}

#ifdef __cplusplus
}
#endif
