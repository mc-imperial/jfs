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

#ifndef JFS_CORE_RNG_H
#define JFS_CORE_RNG_H

#include <cstdint>
#include <random>

namespace jfs {
namespace core {

class RNG {
private:
  std::mt19937_64 generator;

public:
  RNG(uint64_t seed)
      : generator(seed ? seed : std::mt19937_64::default_seed) {}

  // Produce an integer in the range [0, limit).
  uint64_t generate(uint64_t limit);
};

} // jfs
} // core

#endif // JFS_CORE_RNG_H