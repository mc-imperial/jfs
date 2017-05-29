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
#ifndef JFS_CORE_SMTLIB2PARSER_H
#define JFS_CORE_SMTLIB2PARSER_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Query.h"
#include "llvm/ADT/StringRef.h"
#include <memory>

namespace jfs {
namespace core {
class SMTLIB2Parser : public JFSContextErrorHandler {
public:
  SMTLIB2Parser(JFSContext &ctx);
  ~SMTLIB2Parser();
  std::shared_ptr<Query> parseFile(llvm::StringRef fileName);
  virtual ErrorAction handleZ3error(JFSContext &ctx, Z3_error_code ec);

private:
  JFSContext &ctx;
  unsigned errorCount;
};
}
}
#endif
