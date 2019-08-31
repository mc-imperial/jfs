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
#ifndef JFS_TRANSFORM_QUERY_PASS_H
#define JFS_TRANSFORM_QUERY_PASS_H
#include "jfs/Core/Model.h"
#include "jfs/Core/Query.h"
#include "jfs/Support/ICancellable.h"
#include "llvm/ADT/StringRef.h"
#include <atomic>

namespace jfs {
namespace transform {
class QueryPass : jfs::support::ICancellable {
protected:
  std::atomic<bool> cancelled;

public:
  QueryPass() : cancelled(false) {}
  virtual ~QueryPass() {}
  // returns `true` if changed, `false` otherwise.
  virtual bool run(jfs::core::Query&) = 0;
  virtual llvm::StringRef getName() = 0;
  void cancel() override { cancelled = true; }
  virtual bool convertModel(jfs::core::Model* m) = 0;
};
}
}

#endif
