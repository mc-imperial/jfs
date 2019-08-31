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
#include "jfs/Transform/QueryPassManager.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/JFSTimerMacros.h"
#include <atomic>
#include <mutex>
#include <vector>

using namespace jfs::core;

namespace jfs {
namespace transform {
class QueryPassManagerImpl : public jfs::support::ICancellable {
private:
  // This not a std::unique_ptr<QueryPass> because some passes just collect
  // information so clients will need to hold on to a pointer to those
  // passes.  This means we can't have unique ownership (otherwise clients
  // would have to hold on to raw pointers which is dangerous).
  std::vector<std::shared_ptr<QueryPass>> passes;
  std::mutex passesMutex;
  std::atomic<bool> cancelled;

public:
  QueryPassManagerImpl() : cancelled(false) {}
  ~QueryPassManagerImpl() {}
  void add(std::shared_ptr<QueryPass> pass) {
    std::lock_guard<std::mutex> lock(passesMutex);
    passes.push_back(pass);
  }
  // The mutex currently exists just to prevent a race
  // between cancel() and clear().
  void clear() {
    std::lock_guard<std::mutex> lock(passesMutex);
    passes.clear();
  }
  void cancel() {
    std::lock_guard<std::mutex> lock(passesMutex);
    cancelled = true;
    for (auto const& pass : passes) {
      pass->cancel();
    }
  }
  void run(Query &q) {
    // FIXME: We can't hold passesMutex here otherwise `cancel` will not
    // cancel until this method finishes.
    JFSContext &ctx = q.getContext();
    JFS_AG_COL(pass_times, ctx);
    IF_VERB(ctx, ctx.getDebugStream() << "(QueryPassManager starting)\n";);
    for (auto pi = passes.begin(), pe = passes.end(); pi != pe; ++pi) {
      IF_VERB(ctx,
              ctx.getDebugStream()
                  << "(QueryPassManager \"" << (*pi)->getName() << "\")\n";);
      IF_VERB_GT(ctx, 1,
                 ctx.getDebugStream()
                     << ";Before \"" << (*pi)->getName() << "\n"
                     << q << "\n";);
      if (cancelled) {
        IF_VERB(ctx, ctx.getDebugStream() << "(QueryPassManager cancelled)\n";);
        return;
      }
      {
        JFS_AG_TIMER(pass_timer, (*pi)->getName(), pass_times, ctx);
        // Now run the pass
        (*pi)->run(q);
      }

      IF_VERB_GT(ctx, 1,
                 ctx.getDebugStream() << ";After \"" << (*pi)->getName() << "\n"
                                      << q << "\n";);
    }
    IF_VERB(ctx, ctx.getDebugStream() << "(QueryPassManager finished)\n";);
  }

  // FIXME: We should probably make this cancellable.
  bool convertModel(jfs::core::Model* m) {
    std::lock_guard<std::mutex> lock(passesMutex);
    assert(m != nullptr);
    JFSContext& ctx = m->getContext();
    JFS_AG_COL(convert_model_pass_times, ctx);
    IF_VERB(ctx, ctx.getDebugStream()
                     << "(QueryPassManager::convertModel starting)\n";);
    // We have to walk through the passes backwards so that we perform model
    // conversion in the right order.
    for (auto pi = passes.rbegin(), pe = passes.rend(); pi != pe; ++pi) {
      IF_VERB(ctx, ctx.getDebugStream() << "(QueryPassManager::convertModel \""
                                        << (*pi)->getName() << "\")\n";);
      IF_VERB_GT(ctx, 1,
                 ctx.getDebugStream()
                     << ";Before \"" << (*pi)->getName() << "\n"
                     << m->getSMTLIBString() << "\n";);
      // FIXME: In an asserts build we should hold on to a copy of the final
      // query and original query and check that the models satisfy the
      // constraints.
      {
        JFS_AG_TIMER(convert_modenl_pass_timer, (*pi)->getName(),
                     convert_model_pass_times, ctx);
        // Now ask the pass to convert the model.
        bool success = (*pi)->convertModel(m);
        if (!success) {
          ctx.getErrorStream()
              << "(QueryPassManager::convertModel conversion failed with pass "
              << (*pi)->getName() << ")\n";
          return false;
        }
      }

      IF_VERB_GT(ctx, 1,
                 ctx.getDebugStream() << ";After \"" << (*pi)->getName() << "\n"
                                      << m->getSMTLIBString() << "\n";);
    }
    IF_VERB(ctx, ctx.getDebugStream()
                     << "(QueryPassManager::convertModel finished)\n";);
    return true;
  }
};

QueryPassManager::QueryPassManager() : impl(new QueryPassManagerImpl()) {}
QueryPassManager::~QueryPassManager() {}
void QueryPassManager::add(std::shared_ptr<QueryPass> pass) { impl->add(pass); }
void QueryPassManager::run(Query &q) { impl->run(q); }
void QueryPassManager::cancel() { impl->cancel(); }
void QueryPassManager::clear() { impl->clear(); }
bool QueryPassManager::convertModel(jfs::core::Model* m) {
  return impl->convertModel(m);
}
}
}
