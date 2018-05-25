//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_FUZZING_COMMON_FREE_VARIABLE_TO_BUFFER_ASSIGNMENT_PASS_H
#define JFS_FUZZING_COMMON_FREE_VARIABLE_TO_BUFFER_ASSIGNMENT_PASS_H
#include "jfs/Core/Query.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeMap.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/FuzzingCommon/BufferAssignment.h"
#include "jfs/FuzzingCommon/EqualityExtractionPass.h"
#include "jfs/FuzzingCommon/FreeVariableToBufferAssignmentPassOptions.h"
#include "jfs/Transform/QueryPass.h"
#include <vector>

namespace jfs {
namespace fuzzingCommon {

class ConstantAssignment {
public:
  // TODO: Put this behind an interface
  jfs::core::Z3ASTMap<jfs::core::Z3ASTHandle> assignments;
  void print(llvm::raw_ostream&) const;
  void dump() const;
};

class FreeVariableToBufferAssignmentPass : public jfs::transform::QueryPass {
private:
  const EqualityExtractionPass& eep;
  // raw ptr because we don't own storage
  FreeVariableToBufferAssignmentPassOptions* options;
  std::unique_ptr<FreeVariableToBufferAssignmentPassOptions> defaultOptions;

public:
  FreeVariableToBufferAssignmentPass(
      const EqualityExtractionPass&,
      FreeVariableToBufferAssignmentPassOptions* options);
  ~FreeVariableToBufferAssignmentPass() {}
  bool run(jfs::core::Query& q) override;
  virtual llvm::StringRef getName() override;
  // TODO: Put these behind an interface
  std::shared_ptr<BufferAssignment> bufferAssignment;
  // FIXME: It's debatable whether we actually need this. The
  // ConstantPropagation pass
  // means that equalities like this will already be expanded in constraints.
  // This means
  // the free variables that have constant assignments will never be used once
  // the
  // EqualityExtractionPass has run and so constantAssignment is always empty.
  std::shared_ptr<ConstantAssignment> constantAssignments;
};
} // namespace fuzzingCommon
} // namespace jfs

#endif
