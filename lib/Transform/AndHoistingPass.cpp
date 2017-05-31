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
  const JFSContext &ctx = q.getContext();
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

    if (!Z3_is_app(ctx.z3Ctx, e)) {
      // Not an application. Just add as a constraint
      newConstraints.push_back(e);
      continue;
    }

    Z3AppHandle topLevelApp = Z3AppHandle(::Z3_to_app(ctx.z3Ctx, e), ctx.z3Ctx);
    Z3FuncDeclHandle topLevelFunc =
        Z3FuncDeclHandle(::Z3_get_app_decl(ctx.z3Ctx, topLevelApp), ctx.z3Ctx);
    Z3_decl_kind kind = Z3_get_decl_kind(ctx.z3Ctx, topLevelFunc);
    if (kind != Z3_OP_AND) {
      // Not an and. Just add as a constraint
      newConstraints.push_back(e);
      continue;
    }

    // This is an and expression. Push on to work list so we walk the AST.
    changed = true;
    unsigned numArgs = Z3_get_app_num_args(ctx.z3Ctx, topLevelApp);
    assert(numArgs >= 2 && "Unexpected number of args");
    for (unsigned index = 0; index < numArgs; ++index) {
      workList.push_back(Z3ASTHandle(
          ::Z3_get_app_arg(ctx.z3Ctx, topLevelApp, index), ctx.z3Ctx));
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
