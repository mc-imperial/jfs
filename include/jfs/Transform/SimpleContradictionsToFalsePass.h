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
#ifndef JFS_TRANSFORM_SIMPLE_CONTRADICTIONS_TO_FALSE_H
#define JFS_TRANSFORM_SIMPLE_CONTRADICTIONS_TO_FALSE_H
#include "jfs/Core/Query.h"
#include "jfs/Transform/QueryPass.h"

namespace jfs {
namespace transform {
class SimpleContradictionsToFalsePass : public QueryPass {
public:
  SimpleContradictionsToFalsePass() {}
  ~SimpleContradictionsToFalsePass() {}
  bool run(jfs::core::Query& q) override;
  virtual llvm::StringRef getName() override;
  virtual bool convertModel(jfs::core::Model* m) override;
};
}
}

#endif
