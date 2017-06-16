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
    if (!node.isAppOf(Z3_OP_EQ)) {
      // Not an equality. Keep this constraint
      newConstraints.push_back(node);
      continue;
    }
    // Now pattern match the equality for the cases we
    // know we can help the fuzzer
    std::vector<Z3ASTHandle> equalOperands;
    equalOperands.reserve(2);

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

    if (equalOperands.size() == 0) {
      // Equality didn't match pattern. Keep the constraint
      newConstraints.push_back(node);
      continue;
    }

    // Pattern is matched. We won't keep this constraint
    // and will instead record this equality

    // See if we have existing equality set
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

  // Modify constraints
  q.constraints = std::move(newConstraints);
#ifndef NDEBUG
  // Sanity check the equality sets
  for (auto mi = mapping.cbegin(), me = mapping.cend(); mi != me; ++mi) {
    auto equalitySet = mi->second;
    unsigned constantCount =
        std::count_if(equalitySet->cbegin(), equalitySet->cend(),
                      [](Z3ASTHandle e) { return e.isConstant(); });
    assert(constantCount <= 1 &&
           "Can't assert equality over multiple constants");
  }
#endif
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
