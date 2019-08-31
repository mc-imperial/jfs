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
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/RNG.h"
#include "jfs/Support/StatisticsManager.h"
#include "llvm/Support/raw_os_ostream.h"
#include <assert.h>
#include <list>
#include <mutex>
#include <unordered_map>

namespace {
// Forward decl
void z3_error_handler(Z3_context ctx, Z3_error_code ec);
}

namespace jfs {
namespace core {

JFSContextErrorHandler::JFSContextErrorHandler() {}
JFSContextErrorHandler::~JFSContextErrorHandler() {}

class JFSContextImpl {
public:
  // Really this should be private but seeing as this decl is
  // in an implementation file it doesn't matter.
  JFSContext* publicContext;
  std::list<JFSContextErrorHandler*> errorHandlers;
  Z3_context z3Ctx;
  JFSContextConfig config;
  std::unique_ptr<jfs::support::StatisticsManager> stats;
  RNG rng;
  // Global to all instances
  static std::unordered_map<Z3_context, jfs::core::JFSContextImpl*>
      activeContexts;
  static std::mutex activeContextsMutex; // protects
public:
  JFSContextImpl(JFSContext* ctx, const JFSContextConfig& ctxCfg)
      : publicContext(ctx), config(ctxCfg), stats(nullptr),
        rng(ctxCfg.seed) {
    std::lock_guard<std::mutex> lock(activeContextsMutex);
    // TODO use ctxCfg
    Z3_config z3Cfg = Z3_mk_config();
    // Do ref counting of ASTs ourselves
    z3Ctx = Z3_mk_context_rc(z3Cfg);
    Z3_set_error_handler(z3Ctx, z3_error_handler);
    // When emitting Z3 expressions make them SMT-LIBv2 compliant
    Z3_set_ast_print_mode(z3Ctx, Z3_PRINT_SMTLIB2_COMPLIANT);
    Z3_del_config(z3Cfg);
    auto success = activeContexts.insert(std::make_pair(z3Ctx, this));
    assert(success.second && "insert failed");

    // Set up stats
    if (config.gathericStatistics) {
      stats.reset(new jfs::support::StatisticsManager());
    }
  }

  ~JFSContextImpl() {
    std::lock_guard<std::mutex> lock(activeContextsMutex);
    // We have to delete stats before we destroy the Z3
    // context because it might be holding on to Z3 objects.
    stats.reset(nullptr);
    auto it = activeContexts.find(z3Ctx);
    if (it == activeContexts.end()) {
      llvm::errs() << "Context not registered\n";
      abort();
    }
    activeContexts.erase(it);
    Z3_del_context(z3Ctx);
  }

  // Don't allow copying
  JFSContextImpl(const JFSContextImpl&) = delete;
  JFSContextImpl(const JFSContextImpl&&) = delete;
  JFSContextImpl& operator=(const JFSContextImpl&) = delete;

  bool registerErrorHandler(JFSContextErrorHandler* h) {
    errorHandlers.push_front(h);
    return true;
  }

  bool unRegisterErrorHandler(JFSContextErrorHandler* h) {
    bool removed = false;
    for (auto bi = errorHandlers.begin(), be = errorHandlers.end(); bi != be;
         ++bi) {
      if (*bi == h) {
        removed = true;
        errorHandlers.erase(bi);
        break;
      }
    }
    return removed;
  }
  void z3ErrorHandler(Z3_error_code ec) {
    // Call the error handlers in order.
    for (auto bi = errorHandlers.begin(), be = errorHandlers.end(); bi != be;
         ++bi) {
      JFSContextErrorHandler::ErrorAction action =
          (*bi)->handleZ3error(*publicContext, ec);
      if (action == JFSContextErrorHandler::STOP) {
        return;
      }
    }

    // Default behaviour
    getErrorStream() << "JFSContext: Received unhandled Z3 error \""
                     << Z3_get_error_msg(z3Ctx, ec) << "\"\n";
    abort();
  }

  // TODO: Rethink this API.
  unsigned getVerbosity() const { return config.verbosity; }
  // Message streams
  // TODO: Make these customisable
  llvm::raw_ostream& getErrorStream() { return llvm::errs(); }
  llvm::raw_ostream& getWarningStream() { return llvm::errs(); }
  llvm::raw_ostream& getDebugStream() { return llvm::errs(); }

  // FIXME: Should check compiler supports attribute
  // Unlike Z3 errors it is guaranteed that execution will
  // not leave this function.
  __attribute__((noreturn)) void raiseFatalError(llvm::StringRef msg) {
    // Call the error handlers in order.
    for (const auto& eh : errorHandlers) {
      auto action = eh->handleFatalError(*publicContext, msg);
      if (action == JFSContextErrorHandler::STOP) {
        break;
      }
    }
    // Guarantee that execution does not continue
    abort();
  }

  void raiseError(llvm::StringRef msg) {
    // Call the error handlers in order.
    for (const auto& eh : errorHandlers) {
      auto action = eh->handleFatalError(*publicContext, msg);
      if (action == JFSContextErrorHandler::STOP) {
        return;
      }
    }
  }

  jfs::support::StatisticsManager* getStats() const { return stats.get(); }
  const JFSContextConfig& getConfig() const { return config; }
};

std::unordered_map<Z3_context, jfs::core::JFSContextImpl*>
    JFSContextImpl::activeContexts;
std::mutex JFSContextImpl::activeContextsMutex;
}
}

namespace {
// We can't give Z3 a pointer to member function so instead this global
// function handles calling the right JFSContext
void z3_error_handler(Z3_context ctx, Z3_error_code ec) {
  std::lock_guard<std::mutex> lock(
      jfs::core::JFSContextImpl::activeContextsMutex);
  // Find the appropriate JFSContextImpl and notify of error
  auto it = jfs::core::JFSContextImpl::activeContexts.find(ctx);
  if (it == jfs::core::JFSContextImpl::activeContexts.end()) {
    llvm::errs() << "Context not registered\n";
    abort();
  }
  it->second->z3ErrorHandler(ec);
}
}

namespace jfs {
namespace core {

// JFSContext

JFSContext::JFSContext(const JFSContextConfig& ctxCfg)
    : impl(new JFSContextImpl(this, ctxCfg)) {}

JFSContext::~JFSContext() {}

bool JFSContext::operator==(const JFSContext& other) const {
  // We don't allow copying of a JFSContext so the only
  // way a context can be the same is if it has the same
  // memory address.
  return this == &(other);
}

bool JFSContext::registerErrorHandler(JFSContextErrorHandler *h) {
  return impl->registerErrorHandler(h);
}

bool JFSContext::unRegisterErrorHandler(JFSContextErrorHandler *h) {
  return impl->unRegisterErrorHandler(h);
}

void JFSContext::raiseFatalError(llvm::StringRef msg) {
  impl->raiseFatalError(msg);
}

void JFSContext::raiseError(llvm::StringRef msg) { impl->raiseError(msg); }

Z3_context JFSContext::getZ3Ctx() const { return impl->z3Ctx; }

unsigned JFSContext::getVerbosity() const { return impl->config.verbosity; }

llvm::raw_ostream &JFSContext::getErrorStream() {
  return impl->getErrorStream();
}

llvm::raw_ostream &JFSContext::getWarningStream() {
  return impl->getWarningStream();
}

llvm::raw_ostream &JFSContext::getDebugStream() {
  return impl->getDebugStream();
}

jfs::support::StatisticsManager* JFSContext::getStats() const {
  return impl->getStats();
}

const JFSContextConfig& JFSContext::getConfig() const {
  return impl->getConfig();
}

RNG& JFSContext::getRNG() const { return impl->rng; }
}
}
