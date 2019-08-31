//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2017-2018 Alastair Donaldson
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/Core/ModelValidator.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/Core/Z3NodeUtil.h"
#include "llvm/Support/raw_ostream.h"

namespace {
jfs::core::ModelValidationOptions defaultModelValidationOptions;
}

namespace jfs {
namespace core {

const char*
ValidationFailureInfo::reasonAsString(ValidationFailureInfo::ReasonTy reason) {
  switch (reason) {
#define RET_REASON(X)                                                          \
  case ValidationFailureInfo::ReasonTy::X:                                     \
    return #X
    RET_REASON(NO_REASON);
    RET_REASON(EVALUATED_TO_FALSE);
    RET_REASON(EVALUATED_TO_NON_CONSTANT);
    RET_REASON(EVALUATED_TO_NON_BOOL_SORT);
  default:
    llvm_unreachable("Unhandled ValidationFailureInfo::ReasonTy");
#undef RET_REASON
  }
}

ValidationFailureInfo::ValidationFailureInfo(ReasonTy reason, uint64_t index,
                                             Z3ASTHandle constraint,
                                             Model* model)
    : reason(reason), index(index), constraint(constraint), model(model) {}

ValidationFailureInfo::ValidationFailureInfo()
    : reason(ValidationFailureInfo::NO_REASON), index(0), constraint(),
      model(nullptr) {}

ModelValidator::ModelValidator() {}
ModelValidator::~ModelValidator() {}

void ModelValidator::reset() { failures.clear(); }

std::string ModelValidator::toStr() const {
  std::string storage;
  llvm::raw_string_ostream ss(storage);
  ss << "(ModelValidator " << getNumberOfFailures() << " failures";
  if (getNumberOfFailures() == 0) {
    ss << ")\n";
    return ss.str();
  }
  // There were failures
  ss << "\n";
  for (const auto& failure : failures) {
    // TODO: Give a better diagnosis
    ss << "constraint " << failure.index << " : "
       << ValidationFailureInfo::reasonAsString(failure.reason) << "\n";
  }
  ss << ")\n";
  return ss.str();
}

bool ModelValidator::validate(const Query& q, Model* m,
                              const ModelValidationOptions* options) {
  if (m == nullptr) {
    return false;
  }
  if (options == nullptr) {
    options = &defaultModelValidationOptions;
  }
  JFSContext& ctx = q.getContext();
  Z3FuncDeclSet foundDecls;
  if (options->warnOnVariablesMissingAssignment) {
    // Collect the variables used in the query
    Z3NodeUtil::collectFuncDecls(foundDecls, q.constraints.begin(),
                                 q.constraints.end());
    for (const auto& decl : foundDecls) {
      if (!m->hasAssignmentFor(decl)) {
        // TODO: Should we add an option to turn this into a failure?
        // A missing assignment doesn't necessarily indicate a problem.
        // A missing assignment usually means that any assignment should do.
        // Are there any cases where it doesn't?
        ctx.getWarningStream()
            << "(warning model is missing assignment for " << decl.toStr()
            << " )\n";
      }
    }
  }
  for (uint64_t index = 0; index < q.constraints.size(); ++index) {
    Z3ASTHandle constraint = q.constraints[index];
    Z3ASTHandle evaluation = m->evaluate(constraint, /*modelCompletion=*/true);
    IF_VERB(ctx, ctx.getDebugStream()
                     << "(ModelValidator constraint index " << index
                     << " evaluated to " << evaluation.toStr() << ")\n");
    if (!evaluation.isConstant()) {
      // Should be a constant
      failures.emplace_back(ValidationFailureInfo::EVALUATED_TO_NON_CONSTANT,
                            index, constraint, m);
      continue;
    }
    if (!evaluation.getSort().isBoolTy()) {
      failures.emplace_back(ValidationFailureInfo::EVALUATED_TO_NON_BOOL_SORT,
                            index, constraint, m);
      continue;
    }
    // Check the constraint evaluated to true
    if (evaluation.isFalse()) {
      failures.emplace_back(ValidationFailureInfo::EVALUATED_TO_FALSE, index,
                            constraint, m);
    }

    // Constraint evaluated to true
    assert(evaluation.isTrue());
  }
  return true;
}

} // namespace core
} // namespace jfs
