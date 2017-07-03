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
#include "jfs/FuzzingCommon/EqualityExtractionPass.h"
#include <algorithm>
#include <memory>

using namespace jfs::core;

namespace jfs {
namespace fuzzingCommon {

EqualityExtractionPass::EqualityExtractionPass() {}

llvm::StringRef EqualityExtractionPass::getName() {
  return "EqualityExtractionPass";
}

bool EqualityExtractionPass::run(jfs::core::Query &q) {
  JFSContext &ctx = q.getContext();
  mapping.clear();
  equalities.clear();
  // Maps from expr to set of equivalent expressions.
  // NOTE: Multiple keys will map to the same Z3ASTSet
  std::vector<Z3ASTHandle> newConstraints;
  newConstraints.reserve(q.constraints.size());

  for (auto bi = q.constraints.begin(), be = q.constraints.end(); bi != be;
       ++bi) {
    Z3ASTHandle node = *bi;
    // Now pattern match the equality for the cases we
    // know we can help the fuzzer
    std::vector<Z3ASTHandle> equalOperands;
    equalOperands.reserve(2);

    if (node.isFreeVariable() && node.getSort().isBoolTy()) {
      // Match
      // `<variable>` where <variable> has boolean sort
      // this is equivalent to
      // `(= <variable> true)`
      equalOperands.push_back(node);
      equalOperands.push_back(Z3ASTHandle(::Z3_mk_true(ctx.z3Ctx), ctx.z3Ctx));
    } else if (node.isAppOf(Z3_OP_NOT)) {
      // Match
      // `(not <variable>)` where <variable> has boolean sort
      // this is equivalent to
      // `(= <variable> false)`
      Z3ASTHandle child = node.asApp().getKid(0);
      if (child.isFreeVariable() && child.getSort().isBoolTy()) {
        equalOperands.push_back(child);
        equalOperands.push_back(
            Z3ASTHandle(::Z3_mk_false(ctx.z3Ctx), ctx.z3Ctx));
      }
    } else if (node.isAppOf(Z3_OP_EQ)) {
      // Match
      // `(= <variable> <variable>)`
      // `(= <variable> <constant>)`
      // TODO: Match `(= <variable> <sort cast of variable>)`
      // TODO: Match `(= <sort cast of variable> <sort cast of variable>)`
      Z3AppHandle eqApp = node.asApp();
      assert(eqApp.getKind() == Z3_OP_EQ);
      for (unsigned index = 0; index < eqApp.getNumKids(); ++index) {
        Z3ASTHandle kid = eqApp.getKid(index);
        if (kid.isFreeVariable()) {
          // free variable
          equalOperands.push_back(kid);
          continue;
        } else if (kid.isConstant()) {
          // constant operand
          equalOperands.push_back(kid);
          continue;
        }
        // Operand is not accepted.
        // Failed to match the pattern
        equalOperands.clear();
        break;
      }
    }

    if (equalOperands.size() == 0) {
      // Equality didn't match patterns. Keep the constraint
      newConstraints.push_back(node);
      continue;
    }

    // Pattern is matched. We won't keep this constraint
    // and will instead record this equality

    // See if we have an existing equality set
    std::shared_ptr<Z3ASTSet> equalitySet = nullptr;
    for (const auto &e : equalOperands) {
      auto kv = mapping.find(e);
      if (kv != mapping.end()) {
        equalitySet = kv->second;
      }
    }
    if (equalitySet.get() == nullptr) {
      // Need to create new equality set
      equalitySet = std::make_shared<Z3ASTSet>();
      equalities.insert(equalitySet);
    }

    for (auto ei = equalOperands.begin(), ee = equalOperands.end(); ei != ee;
         ++ei) {
      equalitySet->insert(*ei);
    }
    // Now insert the keys into the mapping
    for (auto ei = equalOperands.begin(), ee = equalOperands.end(); ei != ee;
         ++ei) {
      mapping.insert(std::make_pair(*ei, equalitySet));
    }
  }

  if (mapping.size() == 0) {
    // No equalites were found so nothing was changed.
    return false;
  }

  // Do we really want this? Preprocessing steps will probably mean
  // we don't hit this case.
  // Sanity check the equality sets. If there are multiple constants
  // in an equality set we've found an inconsistency.
  for (auto mi = mapping.cbegin(), me = mapping.cend(); mi != me; ++mi) {
    auto equalitySet = mi->second;
    unsigned constantCount =
        std::count_if(equalitySet->cbegin(), equalitySet->cend(),
                      [](Z3ASTHandle e) { return e.isConstant(); });
    if (constantCount > 1) {
      // Found inconsistency. Replace constraints with false
      q.constraints.clear();
      q.constraints.push_back(Z3ASTHandle(::Z3_mk_false(ctx.z3Ctx), ctx.z3Ctx));
      return true;
    }
  }

  // Modify constraints
  q.constraints = std::move(newConstraints);

  if (ctx.getVerbosity() > 0) {
    auto &ss = ctx.getDebugStream();
    ss << "(" << getName() << "\n";
    ss << "  equality sets: " << equalities.size() << "\n";
    if (equalities.size() > 0) {
      ss << "  (\n";
      for (auto &es : equalities) {
        ss << "    (\n";
        const Z3ASTSet &eqSet = *(es.get());
        for (auto &ee : eqSet) {
          ss << "      " << ee.toStr() << "\n";
        }
        ss << "    )\n";
      }
      ss << "  )\n";
    }
  }
  return true;
}
}
}
