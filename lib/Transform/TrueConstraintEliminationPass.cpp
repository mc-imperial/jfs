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
#include "jfs/Transform/TrueConstraintEliminationPass.h"
#include "jfs/Core/IfVerbose.h"
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool TrueConstraintEliminationPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  bool changed = false;
  std::vector<Z3ASTHandle> newConstraints;
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    Z3ASTHandle e = *ci;

    if (cancelled) {
      IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
      return false;
    }

    if (e.isTrue()) {
      // Don't add "true" to constraint set.
      changed = true;
      continue;
    }
    newConstraints.push_back(e);
  }

  if (!changed)
    return false;

  q.constraints = std::move(newConstraints);
  return true;
};

llvm::StringRef TrueConstraintEliminationPass::getName() {
  return "TrueConstraintElimination";
}

bool TrueConstraintEliminationPass::convertModel(jfs::core::Model* m) {
  // This pass preserves equivalence so the model does not need to be
  // converted.
  return true;
}
}
}
