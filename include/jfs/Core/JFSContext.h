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
#ifndef JFS_CORE_JFSCONTEXT_H
#define JFS_CORE_JFSCONTEXT_H
#include "z3.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include <list>

namespace jfs {
namespace core {
struct JFSContextConfig {
  unsigned verbosity = 0;
};

class JFSContext;
class JFSContextErrorHandler {
public:
  enum ErrorAction { STOP, CONTINUE };
  virtual ErrorAction handleZ3error(JFSContext& ctx, Z3_error_code ec) = 0;
  virtual ErrorAction handleFatalError(JFSContext& ctx,
                                       llvm::StringRef msg) = 0;
  virtual ErrorAction handleGenericError(JFSContext& ctx,
                                         llvm::StringRef msg) = 0;
};

class JFSContext {
private:
  std::list<JFSContextErrorHandler*> errorHandlers;
  unsigned verbosity;

public:
  Z3_context z3Ctx;
  JFSContext(const JFSContextConfig& ctxCfg);
  ~JFSContext();

  // Don't allow copying
  JFSContext(const JFSContext&) = delete;
  JFSContext(const JFSContext&&) = delete;
  JFSContext& operator=(const JFSContext&) = delete;

  bool registerErrorHandler(JFSContextErrorHandler* h);
  bool unRegisterErrorHandler(JFSContextErrorHandler* h);
  // FIXME: Should not be public
  void z3ErrorHandler(Z3_error_code ec);

  // TODO: Rethink this API.
  unsigned getVerbosity() const { return verbosity; }
  // Message streams
  llvm::raw_ostream& getErrorStream();
  llvm::raw_ostream& getWarningStream();
  llvm::raw_ostream& getDebugStream();

  // FIXME: Should check compiler supports attribute
  // Unlike Z3 errors it is guaranteed that execution will
  // not leave this function.
  __attribute__((noreturn)) void raiseFatalError(llvm::StringRef msg);

  void raiseError(llvm::StringRef msg);
};
}
}
#endif // JFS_JFSCONTEXT_H
