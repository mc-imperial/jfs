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
#ifndef JFS_TRANSFORM_Z3_QUERY_PASS_H
#define JFS_TRANSFORM_Z3_QUERY_PASS_H
#include "jfs/Core/Query.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Transform/QueryPass.h"

namespace jfs {
namespace transform {
class Z3QueryPass : public QueryPass {
protected:
  Z3_context z3Ctx;
  jfs::core::Z3ApplyResultHandle result;

public:
  Z3QueryPass() : z3Ctx(nullptr) {}
  ~Z3QueryPass() {}
  void cancel() override;
  virtual bool convertModel(jfs::core::Model* m) override;
};
}
}
#endif
