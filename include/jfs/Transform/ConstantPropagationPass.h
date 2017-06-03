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
#ifndef JFS_TRANSFORM_CONSTANT_PROPAGATION_PASS_H
#define JFS_TRANSFORM_CONSTANT_PROPAGATION_PASS_H
#include "jfs/Core/Query.h"
#include "jfs/Transform/QueryPass.h"

namespace jfs {
namespace transform {
class ConstantPropagationPass : public QueryPass {
public:
  ConstantPropagationPass() {}
  ~ConstantPropagationPass() {}
  bool run(jfs::core::Query &q) override;
  virtual llvm::StringRef getName() override;
};
}
}

#endif
