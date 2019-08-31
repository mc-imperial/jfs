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
#ifndef JFS_CORE_MODEL_VALIDATOR_H
#define JFS_CORE_MODEL_VALIDATOR_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Model.h"
#include "jfs/Core/Query.h"
#include "jfs/Core/Z3Node.h"
#include <string>

namespace jfs {
namespace core {

class ValidationFailureInfo {
public:
  enum ReasonTy {
    NO_REASON,
    EVALUATED_TO_FALSE,
    EVALUATED_TO_NON_CONSTANT,
    EVALUATED_TO_NON_BOOL_SORT,
  };
  ReasonTy reason;
  uint64_t index;
  Z3ASTHandle constraint;
  Model* model;
  // TODO: Add methods to allow further debugging.
  // It would be useful to recursively walk the AST
  // to find which assignments are responsible and
  // which part of the subtree is causing the constraint
  // to evaluate to false.
  ValidationFailureInfo(ReasonTy reason, uint64_t index, Z3ASTHandle constraint,
                        Model* model);
  ValidationFailureInfo();
  static const char* reasonAsString(ReasonTy reason);
};

class ModelValidationOptions {
public:
  bool warnOnVariablesMissingAssignment = true;
};

class ModelValidator {
public:
  using VFIContainerTy = std::vector<ValidationFailureInfo>;

private:
  VFIContainerTy failures;

public:
  ModelValidator();
  ~ModelValidator();
  VFIContainerTy::const_iterator cbegin() const { return failures.cbegin(); }
  VFIContainerTy::const_iterator cend() const { return failures.cend(); }
  VFIContainerTy::iterator begin() { return failures.begin(); }
  VFIContainerTy::iterator end() { return failures.end(); }
  uint64_t getNumberOfFailures() const { return failures.size(); }
  void reset();
  bool validate(const Query& q, Model* m,
                const ModelValidationOptions* options = nullptr);
  std::string toStr() const;
};
} // namespace core
} // namespace jfs
#endif
