//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2018 J. Ryan Stinnett
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//

#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/SMTLIB2Parser.h"
#include "jfs/Core/ScopedJFSContextErrorHandler.h"
#include "jfs/Core/ToolErrorHandler.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"
#include "jfs/Support/ErrorMessages.h"
#include "jfs/Support/version.h"
#include "jfs/Transform/BitBlastPass.h"
#include "jfs/Transform/DIMACSOutputPass.h"
#include "jfs/Transform/FpToBvPass.h"
#include "jfs/Transform/SimplificationPass.h"
#include "jfs/Transform/StandardPasses.h"
#include "jfs/Transform/QueryPassManager.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/MemoryBuffer.h"
#include <string>

using namespace jfs::core;
using namespace jfs::fuzzingCommon;
using namespace jfs::transform;

namespace {
llvm::cl::opt<std::string> InputFilename(llvm::cl::Positional,
                                         llvm::cl::desc("<input file>"),
                                         llvm::cl::init("-"));
llvm::cl::opt<unsigned> Verbosity("v", llvm::cl::desc("Verbosity level"),
                                  llvm::cl::init(0));

void printVersion(llvm::raw_ostream& os) {
  os << jfs::support::getVersionString() << "\n";
  os << "\n";
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

  QueryPassManager pm;

  // Add passes that JFS would normally apply before handing off to the fuzzer
  AddStandardPasses(pm);
  auto fai = std::make_shared<FuzzingAnalysisInfo>(nullptr);
  // NOTE: One of the passes added in this step is
  // FreeVariableToBufferAssignmentPass which isn't actually required here, but
  // it does allow us to sanity check the count of booleans with the size of the
  // buffer JFS would create.
  fai->addTo(pm);

  // Convert to bit vectors, then to booleans, and output in DIMACS CNF format
  pm.add(std::make_shared<FpToBvPass>());
  pm.add(std::make_shared<SimplificationPass>());
  pm.add(std::make_shared<BitBlastPass>());
  pm.add(std::make_shared<SimplificationPass>());
  // FIXME: Run this logic internally so we can control output rather than
  // relying on Z3's behavior.
  pm.add(std::make_shared<DIMACSOutputPass>());
  pm.run(*query);

  // Number of boolean variables should match JFS buffer size in bits
  jfs::core::Z3FuncDeclSet variables;
  query->collectFuncDecls(variables);
  auto variablesSize = variables.size();
  auto bits = fai->freeVariableAssignment->bufferAssignment->getTypeBitWidth();
  // NOTE: We can't check for a simple equality here because JFS might represent
  // an FP variable by its full bit width in the fuzzing buffer, while the
  // bit-blasted version may be able to simplify away some bits leaving less
  // variables.
  if (variablesSize > bits) {
    ctx.getWarningStream()
        << "(warning " << variablesSize << " SAT variables larger than " << bits
        << " bits in fuzzing buffer)\n";
  }

  IF_VERB(ctx, ctx.getDebugStream()
      << "(" << bits << " fuzzing bits, " << variablesSize << " variables, 2^"
      << variablesSize << " possible assignments)");

  return 0;
}
