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
#ifndef JFS_FUZZING_COMMON_SORT_CONFORMANCE_PASS_H
#define JFS_FUZZING_COMMON_SORT_CONFORMANCE_PASS_H
#include "jfs/Core/Query.h"
#include "jfs/Transform/QueryPass.h"
#include <functional>

namespace jfs {
namespace fuzzingCommon {
class SortConformanceCheckPass : public jfs::transform::QueryPass {
  bool predicateHeld;
  std::function<bool(jfs::core::Z3SortHandle)> predicate;

public:
  SortConformanceCheckPass(
      std::function<bool(jfs::core::Z3SortHandle)> predicate);
  ~SortConformanceCheckPass() {}
  bool run(jfs::core::Query& q) override;
  virtual llvm::StringRef getName() override;
  bool predicateAlwaysHeld() const { return predicateHeld; }
  void reset() { predicateHeld = false; }
  virtual bool convertModel(jfs::core::Model* m) override;
};
}
}

#endif
