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
#include "jfs/FuzzingCommon/EqualityExtractionPass.h"
#include "jfs/Core/IfVerbose.h"
#include <algorithm>
#include <memory>

using namespace jfs::core;

namespace jfs {
namespace fuzzingCommon {

EqualityExtractionPass::EqualityExtractionPass() {}

llvm::StringRef EqualityExtractionPass::getName() {
  return "EqualityExtractionPass";
}

void EqualityExtractionPass::cleanUp() {
  mapping.clear();
  equalities.clear();
}

bool EqualityExtractionPass::run(jfs::core::Query& q) {
  JFSContext& ctx = q.getContext();
  Z3_context z3Ctx = ctx.getZ3Ctx();
  mapping.clear();
  equalities.clear();
  // Maps from expr to set of equivalent expressions.
  // NOTE: Multiple keys will map to the same Z3ASTSet
  std::vector<Z3ASTHandle> newConstraints;
  newConstraints.reserve(q.constraints.size());

  for (auto bi = q.constraints.begin(), be = q.constraints.end(); bi != be;
       ++bi) {
    Z3ASTHandle node = *bi;

    // TODO: We probably should add more cancellation points.
    if (cancelled) {
      IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
      cleanUp();
      return false;
    }
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
      equalOperands.push_back(Z3ASTHandle(::Z3_mk_true(z3Ctx), z3Ctx));
    } else if (node.isAppOf(Z3_OP_NOT)) {
      // Match
      // `(not <variable>)` where <variable> has boolean sort
      // this is equivalent to
      // `(= <variable> false)`
      Z3ASTHandle child = node.asApp().getKid(0);
      if (child.isFreeVariable() && child.getSort().isBoolTy()) {
        equalOperands.push_back(child);
        equalOperands.push_back(Z3ASTHandle(::Z3_mk_false(z3Ctx), z3Ctx));
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

    // See if we have an existing equality sets.
    // If we match more than one equality set we need to destory
    // one of the existing sets and do a union
    std::vector<std::shared_ptr<Z3ASTSet>> matchingEqualitySets;
    for (const auto& e : equalOperands) {
      auto kv = mapping.find(e);
      if (kv != mapping.end()) {
        matchingEqualitySets.push_back(kv->second);
      }
    }
    std::shared_ptr<Z3ASTSet> equalitySet = nullptr;
    if (matchingEqualitySets.size() <= 1) {
      if (matchingEqualitySets.size() == 0) {
        // Simple case there are no existing equality sets
        // that match. Need to create new equality set
        equalitySet = std::make_shared<Z3ASTSet>();
        equalities.insert(equalitySet);
      } else {
        // Simple case there is just one matching equality set
        equalitySet = matchingEqualitySets[0];
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
    } else if (matchingEqualitySets.size() > 1) {
      // Complex case. There are multiple existing equality
      // sets that match. That means we need to union them
      // and remove all the old mappings.

      // Find the largest set and make that the set which will
      // become the union of the other sets.
      equalitySet = *(std::max_element(matchingEqualitySets.begin(),
                                       matchingEqualitySets.end(),
                                       [](const std::shared_ptr<Z3ASTSet>& a,
                                          const std::shared_ptr<Z3ASTSet>& b) {
                                         return a->size() < b->size();
                                       }));

      // Add the equal operands
      equalitySet->insert(equalOperands.begin(), equalOperands.end());

      // Now union with other sets
      for (const auto& otherEqualitySet : matchingEqualitySets) {
        if (otherEqualitySet.get() == equalitySet.get()) {
          continue;
        }
        // Union otherEqualitySet and equalitySet
        equalitySet->insert(otherEqualitySet->begin(), otherEqualitySet->end());
        // Erase the old equality set
        equalities.erase(otherEqualitySet);
      }
      // Now update all mappings.
      for (const auto& expr : *equalitySet) {
        mapping[expr] = equalitySet;
      }
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
      q.constraints.push_back(Z3ASTHandle(::Z3_mk_false(z3Ctx), z3Ctx));
      return true;
    }
  }

  // Modify constraints
  q.constraints = std::move(newConstraints);

  if (ctx.getVerbosity() > 1) {
    auto& ss = ctx.getDebugStream();
    ss << "(" << getName() << "\n";
    ss << "  equality sets: " << equalities.size() << "\n";
    if (equalities.size() > 0) {
      ss << "  (\n";
      for (auto& es : equalities) {
        ss << "    (\n";
        const Z3ASTSet& eqSet = *(es.get());
        for (auto& ee : eqSet) {
          ss << "      " << ee.toStr() << "\n";
        }
        ss << "    )\n";
      }
      ss << "  )\n";
    }
  }
  return true;
}

bool EqualityExtractionPass::convertModel(jfs::core::Model* model) {
  for (auto& es : equalities) {
    Z3FuncDeclSet needsAssignment;
    Z3ASTSet assignment;
    for (auto& e : *es) {
      if (e.isConstant()) {
        // This is a constant to assign
        assert(assignment.size() == 0);
        auto successIteratorPair = assignment.insert(e);
        assert(successIteratorPair.second && "insertion failed");
        continue;
      }
      assert(e.isFreeVariable());
      // Get the corresponding Z3FuncDecl.
      Z3FuncDeclHandle decl = e.asApp().getFuncDecl();
      if (model->hasAssignmentFor(decl)) {
        // We already have an assignment for this.
        // This implies that all other variables in the equality
        // set should get this assignment.
        assert(assignment.size() == 0);
        Z3ASTHandle assignmentForSet = model->getAssignmentFor(decl);
        assert(!assignmentForSet.isNull());
        auto successIteratorPair = assignment.insert(assignmentForSet);
        assert(successIteratorPair.second && "insertion failed");
        continue;
      }

      // This variable needs an assignment
      auto successIteratorPair = needsAssignment.insert(decl);
      assert(successIteratorPair.second && "insertion failed");
    }
    if (needsAssignment.size() == 0) {
      // Nothing to do
      continue;
    }
    assert(assignment.size() == 0 || assignment.size() == 1);
    if (assignment.size() == 0) {
      // Special case: The supplied model didn't provide an assignment
      // to any decl in the equality set. This implies we can pick any value.
      // We have to add the assignment because model completion won't know
      // the relationship between these variables.
      Z3SortHandle sort = needsAssignment.begin()->getSort();
      // Based on the sort pick a sensible value
      Z3ASTHandle assignmentToUse = Model::getDefaultValueFor(sort);
      auto successIteratorPair = assignment.insert(assignmentToUse);
      assert(successIteratorPair.second && "insertion failed");
    }

    // Now add assignments to model
    assert(assignment.size() == 1);
    Z3ASTHandle assignmentForSet = *(assignment.begin());
    for (auto& decl : needsAssignment) {
      model->addAssignmentFor(decl, assignmentForSet);
    }
  }
  return true;
}
}
}
