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
#include "jfs/Transform/AndHoistingPass.h"
#include "jfs/Core/IfVerbose.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool AndHoistingPass::run(Query &q) {
  JFSContext& ctx = q.getContext();
  bool changed = false;
  std::vector<Z3ASTHandle> newConstraints;
  newConstraints.reserve(q.constraints.size());
  std::list<Z3ASTHandle> workList;
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    workList.push_back(*ci);
  }
  while (workList.size() > 0) {
    Z3ASTHandle e = workList.front();
    workList.pop_front();
    if (cancelled) {
      IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
      return false;
    }
    if (!e.isAppOf(Z3_OP_AND)) {
      // Not an logical and application.
      // Just add as a constraint
      newConstraints.push_back(e);
      continue;
    }
    // This is an and expression. Push on to work list so we walk the AST.
    changed = true;
    assert(e.isApp() && "should be an application");
    Z3AppHandle app = e.asApp();

    unsigned numKids = app.getNumKids();
    assert(numKids >= 2 && "Unexpected number of args");
    for (unsigned index = 0; index < numKids; ++index) {
      // We invert the index so we add the kids right to left to the work list
      // which means when popping from the work list we'll handle the nodes
      // left to right.
      assert(numKids >= (index + 1) && "underflow");
      unsigned invertedIndex = numKids - 1 - index;
      workList.push_front(app.getKid(invertedIndex));
    }
  }

  // We didn't do any hoisting or a cancel was triggered
  // so leave Query untouched.
  if (cancelled) {
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
    return false;
  }
  if (!changed)
    return false;

  q.constraints = std::move(newConstraints);
  return true;
}

llvm::StringRef AndHoistingPass::getName() { return "AndHoisting"; }

bool AndHoistingPass::convertModel(jfs::core::Model* m) {
  // This pass preserves equivalence so the model does not need to be
  // converted.
  return true;
}
}

} // namespace jfs
