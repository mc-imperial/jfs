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
#ifndef JFS_RUNTIME_SMTLIB_CORE_H
#define JFS_RUNTIME_SMTLIB_CORE_H
#include "BufferRef.h"
#include <stdint.h>

// We just use the `bool` type to model SMTLIB semantics
// The mapping is trivial so we don't provide many runtime
// functions.

bool makeBoolFrom(BufferRef<const uint8_t> buffer, const uint64_t lowBit,
                  const uint64_t highBit);
#endif
