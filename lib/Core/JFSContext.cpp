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
#include "jfs/Core/JFSContext.h"
#include "llvm/Support/raw_os_ostream.h"
#include <assert.h>
#include <mutex>
#include <unordered_map>

namespace {
std::unordered_map<Z3_context, jfs::core::JFSContext *> activeContexts;
std::mutex activeContextsMutex; // protects
// We can't give Z3 a pointer to member function so instead this global
// function handles calling the right JFSContext
void z3_error_handler(Z3_context ctx, Z3_error_code ec) {
  std::lock_guard<std::mutex> lock(activeContextsMutex);
  // Find the appropriate JFSContext and notify of error
  auto it = activeContexts.find(ctx);
  if (it == activeContexts.end()) {
    llvm::errs() << "Context not registered\n";
    abort();
  }
  it->second->z3ErrorHandler(ec);
}
}

namespace jfs {
namespace core {
JFSContext::JFSContext(const JFSContextConfig &ctxCfg)
    : verbosity(ctxCfg.verbosity) {
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
}

JFSContext::~JFSContext() {
  std::lock_guard<std::mutex> lock(activeContextsMutex);
  auto it = activeContexts.find(z3Ctx);
  if (it == activeContexts.end()) {
    llvm::errs() << "Context not registered\n";
    abort();
  }
  activeContexts.erase(it);
  Z3_del_context(z3Ctx);
}

bool JFSContext::registerErrorHandler(JFSContextErrorHandler *h) {
  errorHandlers.push_front(h);
  return true;
}

bool JFSContext::unRegisterErrorHandler(JFSContextErrorHandler *h) {
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

void JFSContext::z3ErrorHandler(Z3_error_code ec) {
  // Call the error handlers in order.
  for (auto bi = errorHandlers.begin(), be = errorHandlers.end(); bi != be;
       ++bi) {
    JFSContextErrorHandler::ErrorAction action =
        (*bi)->handleZ3error(*this, ec);
    if (action == JFSContextErrorHandler::STOP) {
      return;
    }
  }

  // Default behaviour
  getErrorStream() << "JFSContext: Received unhandled Z3 error \""
                   << Z3_get_error_msg(z3Ctx, ec) << "\"\n";
  abort();
}

llvm::raw_ostream &JFSContext::getErrorStream() {
  // TODO: Make this customisable
  return llvm::errs();
}

llvm::raw_ostream &JFSContext::getWarningStream() {
  // TODO: Make this customisable
  return llvm::errs();
}

llvm::raw_ostream &JFSContext::getDebugStream() {
  // TODO: Make this customisable
  return llvm::errs();
}
}
}
