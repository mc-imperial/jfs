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

#include "jfs/CXXFuzzingBackend/CXXProgram.h"
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderPass.h"
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/SMTLIB2Parser.h"
#include "jfs/Core/ScopedJFSContextErrorHandler.h"
#include "jfs/Core/ToolErrorHandler.h"
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"
#include "jfs/Support/ErrorMessages.h"
#include "jfs/Support/version.h"
#include "jfs/Transform/QueryPassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

using namespace jfs::core;
using namespace jfs::transform;
using namespace jfs::cxxfb;
using namespace jfs::fuzzingCommon;

namespace {
llvm::cl::opt<std::string> InputFilename(llvm::cl::Positional,
                                         llvm::cl::desc("<input file>"),
                                         llvm::cl::init("-"));
llvm::cl::opt<unsigned> Verbosity("v", llvm::cl::desc("Verbosity level"),
                                  llvm::cl::init(0));

llvm::cl::opt<std::string>
    OutputFile("o", llvm::cl::desc("Output file (default stdout)"),
               llvm::cl::init("-"));

void printVersion() {
  llvm::outs() << jfs::support::getVersionString() << "\n";
  llvm::outs() << "\n";
  llvm::cl::PrintVersionMessage();
  return;
}
}

int main(int argc, char** argv) {
  llvm::cl::SetVersionPrinter(printVersion);
  llvm::cl::ParseCommandLineOptions(argc, argv);

  JFSContextConfig ctxCfg;
  ctxCfg.verbosity = Verbosity;
  JFSContext ctx(ctxCfg);
  auto bufferOrError = llvm::MemoryBuffer::getFileOrSTDIN(InputFilename);
  if (auto error = bufferOrError.getError()) {
    ctx.getErrorStream() << jfs::support::getMessageForFailedOpenFileOrSTDIN(
        InputFilename, error);
    return 1;
  }
  auto buffer(std::move(bufferOrError.get()));

  ToolErrorHandler toolHandler(/*ignoredCanceled=*/false);
  ScopedJFSContextErrorHandler errorHandler(ctx, &toolHandler);
  SMTLIB2Parser parser(ctx);
  auto query = parser.parseMemoryBuffer(std::move(buffer));

  std::error_code ec;
  llvm::raw_fd_ostream output(OutputFile, ec, llvm::sys::fs::F_Excl);
  if (ec) {
    ctx.getErrorStream() << "(error \"Failed to open output stream: "
                         << ec.message() << "\")\n";
    return 1;
  }

  QueryPassManager pm;
  auto info = std::make_shared<FuzzingAnalysisInfo>();
  info->addTo(pm);
  auto programBuilder = std::make_shared<CXXProgramBuilderPass>(info, ctx);
  pm.add(programBuilder);
  pm.run(*query);

  // Print the CXX program
  programBuilder->getProgram()->print(output);
  return 0;
}
