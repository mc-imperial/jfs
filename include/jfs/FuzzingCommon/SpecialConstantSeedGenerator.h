//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_FUZZING_COMMON_SPECIAL_CONSTANT_SEED_GENERATOR_H
#define JFS_FUZZING_COMMON_SPECIAL_CONSTANT_SEED_GENERATOR_H

#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeMap.h"
#include "jfs/FuzzingCommon/SeedGenerator.h"
#include "jfs/FuzzingCommon/SpecialConstantSeedGeneratorStat.h"
#include <vector>

namespace jfs {
namespace core {
class JFSContext;
class Model;
}
}

namespace jfs {
namespace fuzzingCommon {

class BufferElement;
class SeedManager;

// A seed generator that emits special constants based on the sorts used in the
// constraints of the query.
class SpecialConstantSeedGenerator : public SeedGenerator {
  // Inherit constructor
  using SeedGenerator::SeedGenerator;

  void preGenerationCallBack(SeedManager& sm) override;
  void postGenerationCallBack(SeedManager& sm) override;
  bool writeSeed(SeedManager& sm) override;
  bool empty() const override;

private:
  // Track vectors of constants found in constraints by sort.
  jfs::core::Z3SortMap<std::vector<jfs::core::Z3ASTHandle>>
      sortToConstraintConstantMap;
  std::unique_ptr<SpecialConstantSeedGeneratorStat> stats;

  bool chooseBool(core::JFSContext& ctx, const BufferElement& be,
                  core::Model& model);
  bool chooseBitVector(core::JFSContext& ctx, const BufferElement& be,
                       core::Model& model);
  bool chooseFloatingPoint(core::JFSContext& ctx, const BufferElement& be,
                       core::Model& model);
};

} // namespace fuzzingCommon
} // namespace jfs

#endif
