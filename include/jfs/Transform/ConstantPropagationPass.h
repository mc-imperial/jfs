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
#ifndef JFS_TRANSFORM_CONSTANT_PROPAGATION_PASS_H
#define JFS_TRANSFORM_CONSTANT_PROPAGATION_PASS_H
#include "jfs/Core/Query.h"
#include "jfs/Transform/Z3QueryPass.h"

namespace jfs {
namespace transform {
class ConstantPropagationPass : public Z3QueryPass {
public:
  ConstantPropagationPass() {}
  ~ConstantPropagationPass() {}
  bool run(jfs::core::Query& q) override;
  virtual llvm::StringRef getName() override;
};
}
}

#endif
