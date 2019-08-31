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
#include "jfs/Core/SMTLIB2Parser.h"
#include "jfs/Core/ScopedJFSContextErrorHandler.h"
#include "jfs/Core/ToolErrorHandler.h"
#include "jfs/Support/ErrorMessages.h"
#include "jfs/Support/version.h"
#include "jfs/Transform/Passes.h"
#include "jfs/Transform/QueryPassManager.h"
#include "jfs/Transform/StandardPasses.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/raw_ostream.h"
#include <string>

using namespace jfs;
using namespace jfs::core;
using namespace jfs::transform;

namespace {
llvm::cl::opt<std::string> InputFilename(llvm::cl::Positional,
                                         llvm::cl::desc("<input file>"),
                                         llvm::cl::init("-"));
llvm::cl::opt<unsigned> Verbosity("v", llvm::cl::desc("Verbosity level"),
                                  llvm::cl::init(0));

llvm::cl::opt<bool>
    PrintBefore("print-before",
                llvm::cl::desc("Print query before running passes"),
                llvm::cl::init(0));

llvm::cl::opt<std::string>
    OutputFile("o", llvm::cl::desc("Output file (default stdout)"),
               llvm::cl::init("-"));

// FIXME: Implement a PassRegistry like LLVM does so we don't
// have to manually list these
enum QueryPassTy {
  and_hoist,
  simplify,
  duplicate_constraint_elimination,
  true_constraint_elimination,
  simple_contradictions_to_false,
  constant_propagation,
  bv_bound_propagation,
  standard_passes,
};
llvm::cl::list<QueryPassTy> PassList(
    llvm::cl::desc("Available passes:"),
    llvm::cl::values(clEnumValN(and_hoist, "and-hoist", "And hoisting"),
                     clEnumVal(simplify, "Simplify"),
                     clEnumValN(duplicate_constraint_elimination, "dce",
                                "duplicate constraint elimination"),
                     clEnumValN(true_constraint_elimination, "tce",
                                "true constraint elimination"),
                     clEnumValN(simple_contradictions_to_false, "sctf",
                                "simple contradictions to false"),
                     clEnumValN(constant_propagation, "constant-propagation",
                                "constant propagation"),
                     clEnumValN(bv_bound_propagation, "bv-bound-propagation",
                                "Bitvector bound propagation"),
                     clEnumValN(standard_passes, "standard-passes",
                                "Run all standard passes")));

// FIXME: Don't do this manually
unsigned AddPasses(QueryPassManager &pm) {
  unsigned count = 0;
  for (unsigned index = 0; index < PassList.size(); ++index) {
    QueryPassTy passTy = PassList[index];
    ++count;
    switch (passTy) {
    case and_hoist:
      pm.add(std::make_shared<AndHoistingPass>());
      break;
    case simplify:
      pm.add(std::make_shared<SimplificationPass>());
      break;
    case duplicate_constraint_elimination:
      pm.add(std::make_shared<DuplicateConstraintEliminationPass>());
      break;
    case true_constraint_elimination:
      pm.add(std::make_shared<TrueConstraintEliminationPass>());
      break;
    case simple_contradictions_to_false:
      pm.add(std::make_shared<SimpleContradictionsToFalsePass>());
      break;
    case constant_propagation:
      pm.add(std::make_shared<ConstantPropagationPass>());
      break;
    case bv_bound_propagation:
      pm.add(std::make_shared<BvBoundPropagationPass>());
      break;
    case standard_passes:
      // This isn't really a single pass
      jfs::transform::AddStandardPasses(pm);
      break;
    default:
      llvm_unreachable("Unknown pass");
    }
  }
  return count;
}

void printVersion(llvm::raw_ostream& os) {
  os << support::getVersionString() << "\n";
  os << "\n";
  llvm::cl::PrintVersionMessage();
  return;
}

}

int main(int argc, char **argv) {
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
    ctx.getErrorStream() << jfs::support::getMessageForFailedOpenFileForWriting(
        OutputFile, ec);
    return 1;
  }

  // Run standard transformations
  QueryPassManager pm;

  unsigned count = AddPasses(pm);
  if (Verbosity > 0)
    ctx.getDebugStream() << "; Added " << count << " passes\n";
  if (PrintBefore)
    output << *query;
  pm.run(*query);
  output << *query;
  output.close();
  return 0;
}
