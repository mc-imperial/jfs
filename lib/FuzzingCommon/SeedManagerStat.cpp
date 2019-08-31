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
#include "jfs/FuzzingCommon/SeedManagerStat.h"

namespace jfs {
namespace fuzzingCommon {

SeedManagerStat::SeedManagerStat(llvm::StringRef name)
    : JFSStat(SEED_MANAGER, name) {}
SeedManagerStat::~SeedManagerStat() {}

void SeedManagerStat::printYAML(llvm::ScopedPrinter& sp) const {
  sp.indent();
  auto& os = sp.getOStream();
  os << "\n";
  sp.startLine() << "name: " << getName() << "\n";
  sp.startLine() << "num_seeds_generated: " << numSeedsGenerated << "\n";
  sp.unindent();
}
} // namespace fuzzingCommon
} // namespace jfs
