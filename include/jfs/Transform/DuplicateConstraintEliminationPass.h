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
#ifndef JFS_TRANSFORM_DUPLICATE_CONSTRAINT_ELIMINATION_PASS_H
#define JFS_TRANSFORM_DUPLICATE_CONSTRAINT_ELIMINATION_PASS_H
#include "jfs/Core/Query.h"
#include "jfs/Transform/QueryPass.h"

namespace jfs {
namespace transform {
class DuplicateConstraintEliminationPass : public QueryPass {
public:
  DuplicateConstraintEliminationPass() {}
  ~DuplicateConstraintEliminationPass() {}
  bool run(jfs::core::Query& q) override;
  virtual llvm::StringRef getName() override;
  virtual bool convertModel(jfs::core::Model* m) override;
};
}
}
#endif
