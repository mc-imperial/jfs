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
#include "jfs/Core/Model.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

namespace {
jfs::core::ModelPrintOptions defaultModelPrintOptions;
}

namespace jfs {
namespace core {

Model::Model(JFSContext& ctx) : ctx(ctx) {}
Model::~Model() {}

JFSContext& Model::getContext() { return ctx; }

Z3ASTHandle Model::getAssignmentFor(Z3FuncDeclHandle funcDecl) {
  return getRepr().getAssignmentFor(funcDecl);
}

bool Model::hasAssignmentFor(Z3FuncDeclHandle decl) {
  return getRepr().hasAssignmentFor(decl);
}

bool Model::addAssignmentFor(Z3FuncDeclHandle decl, Z3ASTHandle e,
                             bool allowOverwrite) {
  return getRepr().addAssignmentFor(decl, e, allowOverwrite);
}

Z3ASTHandle Model::evaluate(Z3ASTHandle e, bool modelCompletion) {
  return getRepr().evaluate(e, modelCompletion);
}

std::string Model::getSMTLIBString(ModelPrintOptions* opts) {
  if (opts == nullptr) {
    // Use default options if none provided.
    opts = &defaultModelPrintOptions;
  }
  std::string storage;
  llvm::raw_string_ostream ss(storage);
  ss << "("; // Model opening bracket
  if (opts->useModelKeyword) {
    // This doesn't seem to be mentioned in the SMT-LIB v2.5 or v2.6
    // standard but Z3 seems to do it.
    ss << "model ";
  }
  if (!(opts->sortDecls)) {
    // Fast path. Just use Z3's API
    ss << z3Model.toStr();
  } else {
    // Need to collect assignments and sort them by decl name
    using AssignmentPairTy = std::pair<Z3FuncDeclHandle, Z3ASTHandle>;
    std::vector<AssignmentPairTy> assignments;
    uint64_t numAssignments = z3Model.getNumAssignments();
    assignments.reserve(numAssignments);
    for (uint64_t index = 0; index < numAssignments; ++index) {
      auto decl = z3Model.getVariableDeclForIndex(index);
      auto assignment = z3Model.getAssignmentFor(decl);
      assignments.emplace_back(AssignmentPairTy(decl, assignment));
    }
    // Now sort the assignments
    std::sort(assignments.begin(), assignments.end(),
              [](const AssignmentPairTy& a, const AssignmentPairTy& b) {
                return a.first.getName() < b.first.getName();
              });
    const char* indent = "  ";
    if (assignments.size() > 0)
      ss << "\n";
    // Now print the assignments in order
    for (auto& assignmentPair : assignments) {
      auto& decl = assignmentPair.first;
      auto& assignment = assignmentPair.second;
      // TODO: Add options to ModelPrintOptions to control how we show
      // constants (e.g. the format of bitvectors).
      ss << indent << "(define-fun " << decl.getName() << " () "
         << decl.getSort().toStr() << " " << assignment.toStr() << ")\n";
    }
  }
  ss << ")"; // Model closing bracket
  return ss.str();
}

bool Model::replaceRepr(Z3ModelHandle replacement) {
  if (replacement.isNull()) {
    return false;
  }
  if (replacement.getContext() != z3Model.getContext()) {
    return false;
  }
  z3Model = replacement;
  return true;
}

Z3ASTHandle Model::getDefaultValueFor(Z3SortHandle sort) {
  switch (sort.getKind()) {
  case Z3_BOOL_SORT: {
    return Z3ASTHandle::getTrue(sort.getContext());
  }
  case Z3_FLOATING_POINT_SORT: {
    return Z3ASTHandle::getFloatZero(sort);
  }
  case Z3_BV_SORT: {
    return Z3ASTHandle::getBVZero(sort);
  }
  default: { llvm_unreachable("Unhandled sort"); }
  }
}

} // namespace core
} // namespace jfs
