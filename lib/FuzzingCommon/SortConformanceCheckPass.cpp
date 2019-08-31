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
#include "jfs/FuzzingCommon/SortConformanceCheckPass.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/Z3NodeSet.h"
#include <list>

using namespace jfs::core;

namespace jfs {
namespace fuzzingCommon {

SortConformanceCheckPass::SortConformanceCheckPass(
    std::function<bool(jfs::core::Z3SortHandle)> predicate)
    : predicateHeld(false), predicate(predicate) {}

bool SortConformanceCheckPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  std::list<Z3ASTHandle> workList;
  for (auto bi = q.constraints.begin(), be = q.constraints.end(); bi != be;
       ++bi) {
    workList.push_front(*bi);
  }
  // Do DFS to collect variables
  jfs::core::Z3FuncDeclSet variables; // Use a set to avoid duplicates
  Z3ASTSet visited;
  predicateHeld = true;
  while (workList.size() != 0) {
    Z3ASTHandle node = workList.front();
    workList.pop_front();

    if (cancelled) {
      IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
      return false;
    }

    if (visited.count(node) > 0) {
      // Already visited. Skip
      continue;
    }

    // Check sort
    bool predicateAnswer = predicate(node.getSort());
    if (!predicateAnswer) {
      predicateHeld = false;
      break;
    }
    visited.insert(node);

    // Add children to the worklist
    if (!node.isApp())
      continue;
    Z3AppHandle app = node.asApp();
    for (unsigned index = 0; index < app.getNumKids(); ++index) {
      workList.push_front(app.getKid(index));
    }
  }

  return false;
}

llvm::StringRef SortConformanceCheckPass::getName() {
  return "SortConformanceCheckPass";
}

bool SortConformanceCheckPass::convertModel(jfs::core::Model* m) {
  // This pass preserves equivalence so the model does not need to be
  // converted.
  return true;
}
}
}
