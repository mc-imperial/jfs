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

#include "jfs/Core/RNG.h"
#include <random>

namespace jfs {
namespace core {

uint64_t RNG::generate(uint64_t limit) {
  std::uniform_int_distribution<uint64_t> distribution(0, limit - 1);
  return distribution(generator);
}

} // jfs
} // core