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
#include "jfs/Core/SMTLIB2Parser.h"
#include "jfs/Core/ScopedJFSContextErrorHandler.h"
#include "jfs/Support/version.h"
#include "jfs/Transform/QueryPassManager.h"
#include "jfs/Transform/StandardPasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

using namespace jfs;
using namespace jfs::core;
using namespace jfs::transform;

namespace {
llvm::cl::opt<std::string> InputFilename(llvm::cl::Positional,
                                    llvm::cl::desc("<input file>"),
                                    llvm::cl::Required);
llvm::cl::opt<unsigned> Verbosity("v", llvm::cl::desc("Verbosity level"),
                                  llvm::cl::init(0));
}

void printVersion() {
  llvm::outs() << support::getVersionString() << "\n";
  llvm::outs() << "\n";
  llvm::cl::PrintVersionMessage();
  return;
}

class ToolErrorHandler : public JFSContextErrorHandler {
  JFSContextErrorHandler::ErrorAction handleZ3error(JFSContext &ctx,
                                                    Z3_error_code ec) {
    llvm::errs() << "(error \"" << Z3_get_error_msg(ctx.z3Ctx, ec) << "\")\n";
    exit(1);
    return JFSContextErrorHandler::STOP; // Unreachable.
  }
};

int main(int argc, char** argv) {
  llvm::cl::SetVersionPrinter(printVersion);
  llvm::cl::ParseCommandLineOptions(argc, argv);

  JFSContextConfig ctxCfg;
  ctxCfg.verbosity = Verbosity;
  JFSContext ctx(ctxCfg);
  if (!llvm::sys::fs::exists(InputFilename)) {
    llvm::errs() << "(error \"" << InputFilename << " does not exist\")\n";
    return 1;
  }

  ToolErrorHandler toolHandler;
  ScopedJFSContextErrorHandler errorHandler(ctx, &toolHandler);
  SMTLIB2Parser parser(ctx);
  auto query = parser.parseFile(InputFilename);
  if (Verbosity > 0)
    query->dump();

  // Run standard transformations
  QueryPassManager pm;
  AddStandardPasses(pm);
  pm.run(*query);
  if (Verbosity > 0)
    query->dump();
  return 0;
}
