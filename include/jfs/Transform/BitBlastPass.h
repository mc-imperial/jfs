//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_TRANSFORM_BIT_BLAST_PASS_H
#define JFS_TRANSFORM_BIT_BLAST_PASS_H
#include "jfs/Core/Query.h"
#include "jfs/Transform/Z3QueryPass.h"

namespace jfs {
namespace transform {
class BitBlastPass : public Z3QueryPass {
public:
  BitBlastPass() {}
  ~BitBlastPass() {}
  bool run(jfs::core::Query& q) override;
  virtual llvm::StringRef getName() override;
};
}
}

#endif
