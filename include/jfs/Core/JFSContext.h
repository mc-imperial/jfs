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
#ifndef JFS_CORE_JFSCONTEXT_H
#define JFS_CORE_JFSCONTEXT_H
#include "z3.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"

namespace jfs {
namespace support {
class StatisticsManager;
}
}

namespace jfs {
namespace core {
struct JFSContextConfig {
  unsigned verbosity = 0;
  bool gathericStatistics = false;
  uint64_t seed = 1;
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
  JFSContextErrorHandler();
  virtual ~JFSContextErrorHandler();
};

class JFSContextImpl;
class RNG;

class JFSContext {
private:
  const std::unique_ptr<JFSContextImpl> impl;

public:
  JFSContext(const JFSContextConfig& ctxCfg);
  ~JFSContext();

  // Don't allow copying
  JFSContext(const JFSContext&) = delete;
  JFSContext(const JFSContext&&) = delete;
  JFSContext& operator=(const JFSContext&) = delete;

  bool operator==(const JFSContext& other) const;

  bool registerErrorHandler(JFSContextErrorHandler* h);
  bool unRegisterErrorHandler(JFSContextErrorHandler* h);

  Z3_context getZ3Ctx() const;
  // TODO: Rethink this API.
  unsigned getVerbosity() const;
  // Message streams
  llvm::raw_ostream& getErrorStream();
  llvm::raw_ostream& getWarningStream();
  llvm::raw_ostream& getDebugStream();

  // FIXME: Should check compiler supports attribute
  // Unlike Z3 errors it is guaranteed that execution will
  // not leave this function.
  __attribute__((noreturn)) void raiseFatalError(llvm::StringRef msg);

  void raiseError(llvm::StringRef msg);
  jfs::support::StatisticsManager* getStats() const;
  const JFSContextConfig& getConfig() const;
  RNG& getRNG() const;
};
}
}
#endif // JFS_JFSCONTEXT_H
