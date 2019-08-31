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
#ifndef JFS_FUZZING_COMMON_SEED_MANAGER_OPTIONS_H
#define JFS_FUZZING_COMMON_SEED_MANAGER_OPTIONS_H
#include "jfs/FuzzingCommon/SeedGenerator.h"
#include <list>
#include <memory>

namespace jfs {
namespace fuzzingCommon {

class SeedGenerator;

class SeedManagerOptions {
public:
  uint64_t maxSeedSpaceInBytes;
  uint64_t maxNumSeeds;
  std::list<std::unique_ptr<SeedGenerator>> generators;
};

} // namespace fuzzingCommon
} // namespace jfs
#endif
