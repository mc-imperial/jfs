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

#include "jfs/FuzzingCommon/SpecialConstantSeedGenerator.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/FuzzingCommon/SeedManager.h"

using namespace jfs::core;

namespace jfs {
namespace fuzzingCommon {

void SpecialConstantSeedGenerator::preGenerationCallBack(SeedManager& sm) {
  auto query = sm.getCurrentQuery();
  auto& ctx = sm.getContext();

  // Do a DFS to find any constants in the constraints.
  std::list<Z3ASTHandle> workList;
  Z3ASTSet seenExpr;
  for (const auto& c : query->constraints) {
    workList.push_back(c);
  }
  while (workList.size() != 0) {
    Z3ASTHandle node = workList.front();
    workList.pop_front();
    if (seenExpr.count(node) > 0) {
      // Already visited
      continue;
    }
    seenExpr.insert(node);

    // If this is a constant, track it by sort.
    if (node.isConstant()) {
      auto sort = node.getSort();
      if (!sort.isBitVectorTy() && !sort.isFloatingPointTy()) {
        continue;
      }
      auto& constants = sortToConstraintConstantMap[sort];
      constants.push_back(node);
      continue;
    }

    // If this is a function application, visit the arguments.
    if (node.isApp()) {
      Z3AppHandle app = node.asApp();
      for (size_t index = 0; index < app.getNumKids(); index++) {
        workList.push_front(app.getKid(index));
      }
      continue;
    }

    llvm_unreachable("Unexpected node type");
  }

  if (ctx.getVerbosity() > 1) {
    ctx.getDebugStream() << "(Constants found in constraints:)\n";
    for (const auto& sortVectorPair : sortToConstraintConstantMap) {
      const auto& sort = sortVectorPair.first;
      ctx.getDebugStream() << "(Stored for sort: " << sort.toStr() << ")\n";
      for (const auto& constant : sortVectorPair.second) {
        ctx.getDebugStream() << "  (" << constant.toStr() << ")\n";
      }
    }
  }
}

bool SpecialConstantSeedGenerator::writeSeed(SeedManager& sm) {

}

bool SpecialConstantSeedGenerator::empty() const { return true; }

} // namespace fuzzingCommon
} // namespace jfs
