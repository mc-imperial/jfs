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
  virtual ErrorAction handleZ3error(JFSContext &ctx, Z3_error_code ec) = 0;
};

class JFSContext {
private:
  std::list<JFSContextErrorHandler *> errorHandlers;
  unsigned verbosity;

public:
  Z3_context z3Ctx;
  JFSContext(const JFSContextConfig &ctxCfg);
  ~JFSContext();
  bool registerErrorHandler(JFSContextErrorHandler *h);
  bool unRegisterErrorHandler(JFSContextErrorHandler *h);
  // FIXME: Should not be public
  void z3ErrorHandler(Z3_error_code ec);
  unsigned getVerbosity() { return verbosity; }
};
}
}
#endif // JFS_JFSCONTEXT_H
