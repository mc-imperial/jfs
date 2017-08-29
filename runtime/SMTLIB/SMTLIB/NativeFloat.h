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
#ifndef JFS_RUNTIME_SMTLIB_NATIVE_FLOAT_H
#define JFS_RUNTIME_SMTLIB_NATIVE_FLOAT_H
#include "SMTLIB/NativeBitVector.h"
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

typedef float jfs_nr_float32;
typedef double jfs_nr_float64;

uint32_t jfs_nr_float32_get_raw_bits(const jfs_nr_float32 value);
uint64_t jfs_nr_float64_get_raw_bits(const jfs_nr_float64 value);

jfs_nr_float32 jfs_nr_float32_get_infinity(bool positive);
jfs_nr_float64 jfs_nr_float64_get_infinity(bool positive);
jfs_nr_float32 jfs_nr_float32_get_zero(bool positive);
jfs_nr_float64 jfs_nr_float64_get_zero(bool positive);
jfs_nr_float32 jfs_nr_float32_get_nan(bool quiet);
jfs_nr_float64 jfs_nr_float64_get_nan(bool quiet);

bool jfs_nr_float32_is_normal(const jfs_nr_float32 value);
bool jfs_nr_float64_is_normal(const jfs_nr_float64 value);
bool jfs_nr_float32_is_subnormal(const jfs_nr_float32 value);
bool jfs_nr_float64_is_subnormal(const jfs_nr_float64 value);
bool jfs_nr_float32_is_zero(const jfs_nr_float32 value);
bool jfs_nr_float64_is_zero(const jfs_nr_float64 value);
bool jfs_nr_float32_is_infinite(const jfs_nr_float32 value);
bool jfs_nr_float64_is_infinite(const jfs_nr_float64 value);
bool jfs_nr_float32_is_positive(const jfs_nr_float32 value);
bool jfs_nr_float64_is_positive(const jfs_nr_float64 value);
bool jfs_nr_float32_is_negative(const jfs_nr_float32 value);
bool jfs_nr_float64_is_negative(const jfs_nr_float64 value);
bool jfs_nr_float32_is_nan(const jfs_nr_float32 value);
bool jfs_nr_float64_is_nan(const jfs_nr_float64 value);

bool jfs_nr_float32_ieee_equals(const jfs_nr_float32 lhs,
                                const jfs_nr_float32 rhs);
bool jfs_nr_float64_ieee_equals(const jfs_nr_float64 lhs,
                                const jfs_nr_float64 rhs);

bool jfs_nr_float32_smtlib_equals(const jfs_nr_float32 lhs,
                                  const jfs_nr_float32 rhs);
bool jfs_nr_float64_smtlib_equals(const jfs_nr_float64 lhs,
                                  const jfs_nr_float64 rhs);

bool jfs_nr_float32_leq(const jfs_nr_float32 lhs, const jfs_nr_float32 rhs);
bool jfs_nr_float64_leq(const jfs_nr_float64 lhs, const jfs_nr_float64 rhs);
bool jfs_nr_float32_lt(const jfs_nr_float32 lhs, const jfs_nr_float32 rhs);
bool jfs_nr_float64_lt(const jfs_nr_float64 lhs, const jfs_nr_float64 rhs);
bool jfs_nr_float32_gt(const jfs_nr_float32 lhs, const jfs_nr_float32 rhs);
bool jfs_nr_float64_gt(const jfs_nr_float64 lhs, const jfs_nr_float64 rhs);
bool jfs_nr_float32_geq(const jfs_nr_float32 lhs, const jfs_nr_float32 rhs);
bool jfs_nr_float64_geq(const jfs_nr_float64 lhs, const jfs_nr_float64 rhs);

jfs_nr_float32 jfs_nr_bitcast_bv_to_float32(const jfs_nr_bitvector_ty value);
jfs_nr_float64 jfs_nr_bitcast_bv_to_float64(const jfs_nr_bitvector_ty value);

jfs_nr_float32
jfs_nr_convert_from_unsigned_bv_to_float32(const jfs_nr_bitvector_ty value);
jfs_nr_float64
jfs_nr_convert_from_unsigned_bv_to_float64(const jfs_nr_bitvector_ty value);

jfs_nr_float32
jfs_nr_convert_from_signed_bv_to_float32(const jfs_nr_bitvector_ty value);
jfs_nr_float64
jfs_nr_convert_from_signed_bv_to_float64(const jfs_nr_bitvector_ty value);

// Note significand does not contain implicit bit
jfs_nr_float32
jfs_nr_make_float32_from_triple(const jfs_nr_bitvector_ty sign,
                                const jfs_nr_bitvector_ty exponent,
                                const jfs_nr_bitvector_ty significand);

// Note significand does not contain implicit bit
jfs_nr_float64
jfs_nr_make_float64_from_triple(const jfs_nr_bitvector_ty sign,
                                const jfs_nr_bitvector_ty exponent,
                                const jfs_nr_bitvector_ty significand);

jfs_nr_float32 jfs_nr_make_float32_from_buffer(const uint8_t* bufferData,
                                               const uint64_t bufferSize,
                                               const uint64_t lowBit);

jfs_nr_float64 jfs_nr_make_float64_from_buffer(const uint8_t* bufferData,
                                               const uint64_t bufferSize,
                                               const uint64_t lowBit);

#ifdef __cplusplus
}
#endif

#endif
