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
#include "jfs/Transform/SimpleContradictionsToFalsePass.h"
#include "jfs/Core/Z3NodeSet.h"
#include <vector>

using namespace jfs::core;

namespace {
// (a) and (not a) are contradictions
bool simplifyTopLevelNot(Query &q) {
  Z3ASTSet seenExpr;
  seenExpr.reserve(q.constraints.size());
  const JFSContext &ctx = q.getContext();
  // First gather all the expressions
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    seenExpr.insert(*ci);
  }

  // Now walk through again seeing if we see (not <expr>) where `<expr>` is
  // something we've already seen.
  Z3ASTSet contradictingConstraints;
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    Z3ASTHandle e = *ci;

    if (!Z3_is_app(ctx.z3Ctx, e))
      continue;

    Z3AppHandle topLevelApp = Z3AppHandle(::Z3_to_app(ctx.z3Ctx, e), ctx.z3Ctx);
    Z3FuncDeclHandle topLevelFunc =
        Z3FuncDeclHandle(::Z3_get_app_decl(ctx.z3Ctx, topLevelApp), ctx.z3Ctx);
    Z3_decl_kind kind = Z3_get_decl_kind(ctx.z3Ctx, topLevelFunc);
    if (kind != Z3_OP_NOT)
      continue;

    // Not expr
    assert(Z3_get_app_num_args(ctx.z3Ctx, topLevelApp) == 1 &&
           "wrong number of args");
    Z3ASTHandle notExprChild =
        Z3ASTHandle(::Z3_get_app_arg(ctx.z3Ctx, topLevelApp, 0), ctx.z3Ctx);
    if (seenExpr.count(notExprChild) == 0)
      continue;

    // Found a contradiction. The constraints contain
    // (e) and (not e).
    contradictingConstraints.insert(e);
    contradictingConstraints.insert(notExprChild);
  }

  if (contradictingConstraints.size() == 0)
    return false;

  // There were contradictions
  std::vector<Z3ASTHandle> newConstraints;
  assert(q.constraints.size() >= newConstraints.size() &&
         "newConstraints was too large");
  newConstraints.reserve(q.constraints.size() - newConstraints.size());
  for (auto ci = q.constraints.cbegin(), ce = q.constraints.cend(); ci != ce;
       ++ci) {
    if (contradictingConstraints.count(*ci) > 0) {
      // Replace contradicting constraint with false
      newConstraints.push_back(
          Z3ASTHandle(::Z3_mk_false(ctx.z3Ctx), ctx.z3Ctx));
      continue;
    }
    // Not detected as a contradiction. Keep this constraint
    newConstraints.push_back(*ci);
  }
  q.constraints = std::move(newConstraints);
  return true;
}
}

namespace jfs {
namespace transform {

bool SimpleContradictionsToFalsePass::run(Query &q) {
  bool changed = false;
  // TODO: Look for other patterns that are contradictions
  changed |= simplifyTopLevelNot(q);
  // TODO: Look for equality contradictions
  // TODO: Look for range contradictions. e.g. x> 5 and x < 5
  return changed;
}

llvm::StringRef SimpleContradictionsToFalsePass::getName() {
  return "SimpleContradictionsToFalse";
}
}
}
