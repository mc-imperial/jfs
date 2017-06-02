//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/Transform/AndHoistingPass.h"
#include <list>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {

bool AndHoistingPass::run(Query &q) {
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

    assert(app.getNumKids() >= 2 && "Unexpected number of args");
    for (unsigned index = 0; index < app.getNumKids(); ++index) {
      workList.push_front(app.getKid(index));
    }
  }

  // We didn't do any hoisting so leave Query untouched.
  if (!changed)
    return false;

  q.constraints = std::move(newConstraints);
  return true;
}

llvm::StringRef AndHoistingPass::getName() { return "AndHoisting"; }
}
}
