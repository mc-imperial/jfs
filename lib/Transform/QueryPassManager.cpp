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
#include "jfs/Transform/QueryPassManager.h"
#include "jfs/Core/IfVerbose.h"
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {
class QueryPassManagerImpl {
private:
  // This not a std::unique_ptr<QueryPass> because some passes just collect
  // information so clients will need to hold on to a pointer to those
  // passes.  This means we can't have unique ownership (otherwise clients
  // would have to hold on to raw pointers which is dangerous).
  std::vector<std::shared_ptr<QueryPass>> passes;

public:
  QueryPassManagerImpl() {}
  ~QueryPassManagerImpl() {}
  void add(std::shared_ptr<QueryPass> pass) { passes.push_back(pass); }
  void run(Query &q) {
    const JFSContext &ctx = q.getContext();
    IF_VERB(ctx, llvm::errs() << "(QueryPassManager starting)\n";);
    for (auto pi = passes.begin(), pe = passes.end(); pi != pe; ++pi) {
      IF_VERB(ctx,
              llvm::errs() << "(QueryPassManager \"" << (*pi)->getName()
                           << "\")\n";);
      IF_VERB_GT(ctx, 1,
                 llvm::errs() << ";Before \"" << (*pi)->getName() << "\n"
                              << q << "\n";);

      // Now run the pass
      (*pi)->run(q);

      IF_VERB_GT(ctx, 1,
                 llvm::errs() << ";After \"" << (*pi)->getName() << "\n"
                              << q << "\n";);
    }
    IF_VERB(ctx, llvm::errs() << "(QueryPassManager finished)\n";);
  }
};

QueryPassManager::QueryPassManager() : impl(new QueryPassManagerImpl()) {}
QueryPassManager::~QueryPassManager() {}
void QueryPassManager::add(std::shared_ptr<QueryPass> pass) { impl->add(pass); }
void QueryPassManager::run(Query &q) { impl->run(q); }
}
}
