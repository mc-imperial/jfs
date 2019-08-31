//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2017-2018 Alastair Donaldson
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/FuzzingCommon/SpecialConstantSeedGeneratorStat.h"

namespace jfs {
namespace fuzzingCommon {

SpecialConstantSeedGeneratorStat::SpecialConstantSeedGeneratorStat(
    llvm::StringRef name)
    : JFSStat(SEED_GENERATOR, name) {}

SpecialConstantSeedGeneratorStat::~SpecialConstantSeedGeneratorStat() {}

void SpecialConstantSeedGeneratorStat::printYAML(
    llvm::ScopedPrinter& sp) const {
  sp.indent();
  auto& os = sp.getOStream();
  os << "\n";
  sp.startLine() << "name: " << getName() << "\n";
  sp.startLine() << "total_built_in_bv_constants: "
                 << totalNumBuiltInBVConstants << "\n";
  sp.startLine() << "num_covered_built_in_bv_constant: "
                 << numCoveredBVConstants << "\n";
  assert(numCoveredBVConstants <= totalNumBuiltInBVConstants);
  sp.startLine() << "total_built_in_fp_constants: "
                 << totalNumBuiltInFPConstants << "\n";
  sp.startLine() << "num_covered_built_in_fp_constant: "
                 << numCoveredFPConstants << "\n";
  assert(numCoveredFPConstants <= totalNumBuiltInFPConstants);
  sp.startLine() << "total_built_in_bool_constants: "
                 << totalNumBuiltInBoolConstants << "\n";
  sp.startLine() << "num_covered_built_in_bv_constant: "
                 << numCoveredBoolConstants << "\n";
  assert(numCoveredBoolConstants <= totalNumBuiltInBVConstants);
  if (foundConstantsCount.size() > 0) {
    sp.startLine() << "num_constants_by_sort:\n";
    sp.indent();
    for (const auto& pair : foundConstantsCount) {
      sp.startLine() << "\"" << pair.first.toStr() << "\": " << pair.second
                     << "\n";
    }
    sp.unindent();
  }
  sp.unindent();
}

} // namespace fuzzingCommon
} // namespace jfs
