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
#ifndef JFS_FUZZING_COMMON_CMDLINE_SEED_MANAGER_OPTIONS_BUILDER_H
#define JFS_FUZZING_COMMON_CMDLINE_SEED_MANAGER_OPTIONS_BUILDER_H
#include "jfs/FuzzingCommon/SeedManager.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {
namespace cl {

std::unique_ptr<jfs::fuzzingCommon::SeedManagerOptions>
buildSeedManagerOptionsFromCmdLine();
}
} // namespace fuzzingCommon
} // namespace jfs

#endif
