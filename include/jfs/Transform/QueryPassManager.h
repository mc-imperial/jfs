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
#ifndef JFS_TRANSFORM_QUERY_PASS_MANAGER_H
#define JFS_TRANSFORM_QUERY_PASS_MANAGER_H
#include "jfs/Core/Model.h"
#include "jfs/Support/ICancellable.h"
#include "jfs/Transform/QueryPass.h"
#include <memory>

namespace jfs {
namespace transform {

class QueryPassManagerImpl;
class QueryPassManager : public jfs::support::ICancellable {
private:
  std::unique_ptr<QueryPassManagerImpl> impl;
public:
  QueryPassManager();
  virtual ~QueryPassManager();
  // This not a std::unique_ptr<QueryPass> because some passes just collect
  // information so clients will need to hold on to a pointer to those
  // passes.  This means we can't have unique ownership (otherwise clients
  // would have to hold on to raw pointers which is dangerous).
  void add(std::shared_ptr<QueryPass> pass);
  void run(jfs::core::Query& q);
  void cancel() override;
  void clear();
  // Modify (in-place) the provided model so that it is a solution to the Query
  // passed to the last call to `run()` before it was modified. It is assumed
  // that the provided model already satisfies the modified query.
  bool convertModel(jfs::core::Model* m);
};
}
}

#endif
