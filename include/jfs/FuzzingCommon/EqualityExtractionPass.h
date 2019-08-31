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
#ifndef JFS_FUZZING_COMMON_EQUALITY_EXTRACTION_PASS_H
#define JFS_FUZZING_COMMON_EQUALITY_EXTRACTION_PASS_H
#include "jfs/Core/Query.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeMap.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/Transform/QueryPass.h"
#include <vector>

namespace jfs {
namespace fuzzingCommon {

// This pass looks for simple equalities (e.g. `(= a b)`), removes them from
// the query and adds them to the known set of equalites. The motivation is
// that the fuzzer is very unlikely to guess at random to make two expressions
// equal. Instead of enforcing them as branch conditions we can construct the
// input program such the equality always holds in some simple cases.
class EqualityExtractionPass : public jfs::transform::QueryPass {
private:
  void cleanUp();

public:
  // TODO: Put this behind an interface once we know what the requirements
  // are.
  jfs::core::Z3ASTMap<std::shared_ptr<jfs::core::Z3ASTSet>> mapping;
  std::unordered_set<std::shared_ptr<jfs::core::Z3ASTSet>> equalities;
  EqualityExtractionPass();
  ~EqualityExtractionPass() {}
  bool run(jfs::core::Query& q) override;
  virtual llvm::StringRef getName() override;
  virtual bool convertModel(jfs::core::Model* m) override;
};
}
}

#endif
