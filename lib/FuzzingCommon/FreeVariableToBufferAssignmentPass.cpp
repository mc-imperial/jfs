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
#include "jfs/FuzzingCommon/FreeVariableToBufferAssignmentPass.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/FuzzingCommon/CommandLineCategory.h"
#include "llvm/Support/CommandLine.h"
#include <algorithm>
#include <list>
#include <vector>

using namespace jfs::core;

namespace {
// TODO: Once we figure out a good strategy we can make picking
// them part of the API rather than a command line option.
enum FreeVariableSortStrategyTy {
  ALPHABETICAL,
  FIRST_OBSERVED,
  NONE, // Warning: Will likely be non-deterministic
};
llvm::cl::opt<FreeVariableSortStrategyTy> FreeVariableSortStrategy(
    "sort-free-variable-strategy",
    llvm::cl::desc("Ordering of free variables in fuzzing buffer"),
    llvm::cl::values(
        clEnumValN(ALPHABETICAL, "alphabetical",
                   "Sort free variables alphabetically (slow)"),
        clEnumValN(FIRST_OBSERVED, "first_observed",
                   "sort free variables by observation order (default)"),
        clEnumValN(NONE, "none", "Do not order. This is non-deterministic")),
    llvm::cl::init(FIRST_OBSERVED),
    llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));
}

namespace jfs {
namespace fuzzingCommon {

BufferElement::BufferElement(const Z3ASTHandle declApp) : declApp(declApp) {
  assert(declApp.isApp() && "should be an application");
  assert(declApp.asApp().isFreeVariable() && "should be an application");
}

unsigned BufferElement::getBitWidth() const {
  Z3SortHandle sort = declApp.getSort();
  switch (sort.getKind()) {
  case Z3_BOOL_SORT:
    // TODO: Investigate whether 1 or 8 is a better choice
    return 1;
  case Z3_BV_SORT:
    return sort.getBitVectorWidth();
  default:
    llvm_unreachable("Unhandled sort");
  }
}

Z3FuncDeclHandle BufferElement::getDecl() const {
  return declApp.asApp().getFuncDecl();
}

std::string BufferElement::getName() const {
  return getDecl().getName();
}

Z3SortHandle BufferElement::getSort() const {
  return declApp.getSort();
}

void BufferElement::print(llvm::raw_ostream& os) const {
  os << "(" << getDecl().getName() << ":" << getBitWidth();
  if (equalities.size() > 0) {
    os << " equalities: ";
    for (const auto& e : equalities) {
      os << " (" << e.toStr() << ")";
    }
  }
  os << ")\n";
}

void BufferElement::dump() const { print(llvm::errs()); }

void BufferAssignment::appendElement(BufferElement& el) {
  chunks.push_back(el);
}

// FIXME: We are assuming everything can aligned to a bit boundary.
// This might not be correct.
unsigned BufferAssignment::computeWidth() const {
  unsigned totalWidth = 0;
  for (const auto& ba : chunks) {
    totalWidth += ba.getBitWidth();
  }
  return totalWidth;
}

void BufferAssignment::print(llvm::raw_ostream& os) const {
  os << "(BufferAssignment " << computeWidth() << " bits\n";
  for (const auto& be : chunks) {
    os << "  ";
    be.print(os);
  }
  os << ")\n";
}

void BufferAssignment::dump() const { print(llvm::errs()); }

void ConstantAssignment::print(llvm::raw_ostream& os) const {
  os << "(ConstantAssignment " << assignments.size() << " entries";
  if (assignments.size() > 0)
    os << "\n";
  for (const auto& kvp : assignments) {
    assert(kvp.first.isApp() && "key must be application");
    assert(kvp.first.isFreeVariable() && "key must be free variable");
    os << "  [" << kvp.first.asApp().getFuncDecl().getName()
       << "] = " << kvp.second.toStr() << "\n";
  }
  os << ")\n";
}

void ConstantAssignment::dump() const { print(llvm::errs()); }

FreeVariableToBufferAssignmentPass::FreeVariableToBufferAssignmentPass(
    const EqualityExtractionPass& eep)
    : eep(eep) {}

llvm::StringRef FreeVariableToBufferAssignmentPass::getName() {
  return "FreeVariableToBufferAssignmentPass";
}

bool FreeVariableToBufferAssignmentPass::run(jfs::core::Query& q) {
  JFSContext& ctx = q.getContext();
  // Do DFS to find all free variables
  Z3ASTSet seenExpr;
  // NOTE: We don't store the Z3FuncDeclHandle, instead we
  // store the applications of it and assume that Z3, "uniques"
  // these for us.
  Z3ASTSet freeVariableApps;
  // This contains the same ASTs as `freeVariableApps` but gives
  // a deterministic ordering.
  std::vector<Z3ASTHandle> orderedFreeVariableApps;

  std::list<Z3ASTHandle> workList;
  for (const auto& c : q.constraints) {
    workList.push_back(c);
  }
  while (workList.size() > 0) {
    Z3ASTHandle node = workList.front();
    workList.pop_front();

    // TODO: Should probably add more cancellation points.
    if (cancelled) {
      IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
      return false;
    }

    if (seenExpr.count(node) > 0) {
      // Visited this Expr before
      continue;
    }
    seenExpr.insert(node);
    if (node.isFreeVariable()) {
      auto itSucPair = freeVariableApps.insert(node);
      if (itSucPair.second && FreeVariableSortStrategy == FIRST_OBSERVED) {
        // This is the first time we've observed this free variable
        // and we are using the "first observed" ordering strategy
        // so add the free variable to the ordered list.
        orderedFreeVariableApps.push_back(node);
      }
      continue;
    }
    if (!node.isApp()) {
      continue;
    }
    Z3AppHandle asApp = node.asApp();
    // Must be an application. Add its arguments to the work list
    for (unsigned index = 0; index < asApp.getNumKids(); ++index) {
      workList.push_front(asApp.getKid((asApp.getNumKids() - 1) - index));
    }
  }

  // Now pick a deterministic ordering
  // TODO: We should think about what strategy is the best here.
  // Now sort them

  // Apply sort strategy.
  // FIXME: This should be refactored so it can be changed by an API. Not
  // on the command line.
  switch (FreeVariableSortStrategy) {
  case ALPHABETICAL: {
    // This strategy scales very poorly with a large number of free variables.
    assert(orderedFreeVariableApps.size() == 0);
    orderedFreeVariableApps.insert(orderedFreeVariableApps.end(),
                                   freeVariableApps.cbegin(),
                                   freeVariableApps.cend());
    std::sort(orderedFreeVariableApps.begin(), orderedFreeVariableApps.end(),
              [](const Z3ASTHandle& a, const Z3ASTHandle& b) {
                return a.asApp().getFuncDecl().toStr() <
                       b.asApp().getFuncDecl().toStr();
              });
    break;
  }
  case NONE: {
    assert(orderedFreeVariableApps.size() == 0);
    orderedFreeVariableApps.insert(orderedFreeVariableApps.end(),
                                   freeVariableApps.cbegin(),
                                   freeVariableApps.cend());
    // Add with non-deterministic ordering
    break;
  }
  case FIRST_OBSERVED: {
    // Nothing to do
    assert(orderedFreeVariableApps.size() == freeVariableApps.size());
    break;
  }
  default:
    llvm_unreachable("Unknown sort strategy");
  }

  // Now record the buffer assignment taking into account equalities
  // NOTE: This approach means that equalities that aren't used in
  // the query are not added. From a fuzzing perspective this means
  // those equalites don't need to be considered because they can be
  // trivialled satisfied.
  bufferAssignment = std::make_shared<BufferAssignment>();
  constantAssignments = std::make_shared<ConstantAssignment>();
  Z3ASTSet alreadyAssigned; // Already assigned to constant map or buffer
  for (const auto& freeVarApp : orderedFreeVariableApps) {
    if (cancelled) {
      IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n");
      return false;
    }

    if (alreadyAssigned.count(freeVarApp) > 0) {
      // We have already assigned this variable a position
      // in the buffer.
      continue;
    }
    alreadyAssigned.insert(freeVarApp);

    assert(freeVarApp.isFreeVariable());
    // See if this variable belongs to a set of known equalities.
    const auto equalitySetsIt = eep.mapping.find(freeVarApp);
    if (equalitySetsIt == eep.mapping.end()) {
      // No equalites so append to buffer
      BufferElement el(freeVarApp);
      bufferAssignment->appendElement(el);
      continue;
    }

    // Equalites
    // We need to now decide which free variable is represent
    // in the buffer and what will be derived from it.
    // FIXME: We are very tightly coupled to the EqualityExtractionPass
    // here. Can this be fixed?

    // Handle constant assignment case.
    Z3ASTHandle foundConstant;
    const Z3ASTSet& equalitySet = *((*equalitySetsIt).second.get());
    // FIXME: Should add assert that we only see one constant
    for (const auto& e : equalitySet) {
      if (e.isConstant()) {
        foundConstant = e;
        break;
      }
    }
    if (!foundConstant.isNull()) {
      // This variable belongs to an equality set that contains
      // a constant. This means that we shouldn't assign this
      // variable to the buffer. Instead we should add it to
      // constant assignment map
      for (const auto& e : equalitySet) {
        if (e == foundConstant) {
          continue;
        }
        // FIXME: When EqualityExtractionPass supports free variable
        // casts we will need to figure out how to handle this.
        assert(e.isFreeVariable() && "key must be free variable");
        auto itSuc = constantAssignments->assignments.insert(
            std::make_pair(e, foundConstant));
        assert(itSuc.second && "constant table cannot already have assignment");
        alreadyAssigned.insert(e);
      }
      continue;
    }

    // The variable needs to be assigned to the buffer but there
    // are equalities that need to be enforced.
    BufferElement el(freeVarApp);
    for (const auto& e : equalitySet) {
      if (e == freeVarApp) {
        continue;
      }
      el.equalities.push_back(e);
      alreadyAssigned.insert(e);
    }
    bufferAssignment->appendElement(el);
  }

  if (ctx.getVerbosity() > 1) {
    bufferAssignment->print(ctx.getDebugStream());
    constantAssignments->print(ctx.getDebugStream());
  }
  return false;
}
}
}
