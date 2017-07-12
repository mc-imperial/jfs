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
#include "jfs/CXXFuzzingBackend/CXXFuzzingSolver.h"
#include "jfs/CXXFuzzingBackend/CXXFuzzingSolverOptions.h"
#include "jfs/CXXFuzzingBackend/ClangOptions.h"
#include "jfs/CXXFuzzingBackend/CmdLine/ClangOptionsBuilder.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/SMTLIB2Parser.h"
#include "jfs/Core/ScopedJFSContextErrorHandler.h"
#include "jfs/Core/ToolErrorHandler.h"
#include "jfs/FuzzingCommon/CmdLine/LibFuzzerOptionsBuilder.h"
#include "jfs/FuzzingCommon/DummyFuzzingSolver.h"
#include "jfs/Support/ErrorMessages.h"
#include "jfs/Support/ScopedTimer.h"
#include "jfs/Support/version.h"
#include "jfs/Transform/QueryPassManager.h"
#include "jfs/Transform/StandardPasses.h"
#include "jfs/Z3Backend/Z3Solver.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/Signals.h"
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

llvm::cl::opt<unsigned>
    MaxTime("max-time", llvm::cl::desc("Max allowed solver time (seconds). "
                                       "Default is 0 which means no maximum"),
            llvm::cl::init(0));

llvm::cl::opt<std::string> OutputDirectory(
    "output-dir", llvm::cl::init(""),
    llvm::cl::desc("Output directory. If not set automatically create one"));

llvm::cl::opt<bool>
    KeepOutputDirectory("keep-output-dir", llvm::cl::init(false),
                        llvm::cl::desc("Keep output directory (default false)"));

enum BackendTy {
  DUMMY_FUZZING_SOLVER,
  Z3_SOLVER,
  CXX_FUZZING_SOLVER,
};

llvm::cl::opt<BackendTy> SolverBackend(
    llvm::cl::desc("Solver backend"),
    llvm::cl::values(clEnumValN(DUMMY_FUZZING_SOLVER, "dummy", "dummy solver"),
                     clEnumValN(Z3_SOLVER, "z3", "Z3 backend"),
                     clEnumValN(CXX_FUZZING_SOLVER, "cxx",
                                "CXX fuzzing backend (default)")),
    llvm::cl::init(CXX_FUZZING_SOLVER));
}

void printVersion() {
  llvm::outs() << support::getVersionString() << "\n";
  llvm::outs() << "\n";
  llvm::cl::PrintVersionMessage();
  return;
}

std::function<void(void)> cancelFn;

void handleInterrupt() {
  if (cancelFn)
    cancelFn();
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

  // FIXME: We assume that parsing is quick so it isn't included
  // as part of the timeout.
  ToolErrorHandler toolHandler(/*ignoreCanceled*/ true);
  ScopedJFSContextErrorHandler errorHandler(ctx, &toolHandler);
  SMTLIB2Parser parser(ctx);
  auto query = parser.parseMemoryBuffer(std::move(buffer));
  if (Verbosity > 10)
    ctx.getDebugStream() << *query;

  // Create pass manager
  QueryPassManager pm;

  // Create the working directory
  std::unique_ptr<jfs::fuzzingCommon::WorkingDirectoryManager> wdm(nullptr);
  if (OutputDirectory.size() > 0) {
    // Use user specified path for working directory
    wdm = jfs::fuzzingCommon::WorkingDirectoryManager::makeAtPath(
        OutputDirectory, ctx, !KeepOutputDirectory);
  } else {
    // Use the current working directory as the base directory
    // and use as a prefix the name of the query.
    llvm::SmallVector<char, 256> currentDir;
    if (auto ec = llvm::sys::fs::current_path(currentDir)) {
      ctx.getErrorStream()
          << "(error failed to get current workding directory because "
          << ec.message() << ")\n";
      exit(1);
    }
    llvm::StringRef currentDirAsStringRef(currentDir.data(), currentDir.size());
    llvm::StringRef prefix;
    if (InputFilename == "-") {
      prefix = "stdin";
    } else {
      // Not on standard input so get the name
      prefix = llvm::sys::path::filename(InputFilename);
    }
    wdm = jfs::fuzzingCommon::WorkingDirectoryManager::makeInDirectory(
        /*directory=*/currentDirAsStringRef, /*prefix=*/prefix, ctx,
        !KeepOutputDirectory);
  }

  // Create solver
  // TODO: Refactor this so it can be used elsewhere
  std::unique_ptr<Solver> solver;
  switch (SolverBackend) {
  case DUMMY_FUZZING_SOLVER: {
    std::unique_ptr<SolverOptions> solverOptions(new SolverOptions());
    solver.reset(new jfs::fuzzingCommon::DummyFuzzingSolver(
        std::move(solverOptions), std::move(wdm), ctx));
    break;
  }
  case Z3_SOLVER: {
    std::unique_ptr<SolverOptions> solverOptions(new SolverOptions());
    solver.reset(new jfs::z3Backend::Z3Solver(std::move(solverOptions), ctx));
    break;
  }
  case CXX_FUZZING_SOLVER: {
    // Tell ClangOptions to try and infer all paths
    std::string pathToExecutable = llvm::sys::fs::getMainExecutable(
        argv[0], reinterpret_cast<void*>(reinterpret_cast<intptr_t>(main)));
    auto clangOptions =
        jfs::cxxfb::cl::buildClangOptionsFromCmdLine(pathToExecutable);
    IF_VERB(ctx, clangOptions->print(ctx.getDebugStream()));

    auto libFuzzerOptions =
        jfs::fuzzingCommon::cl::buildLibFuzzerOptionsFromCmdLine();

    std::unique_ptr<jfs::cxxfb::CXXFuzzingSolverOptions> solverOptions(
        new jfs::cxxfb::CXXFuzzingSolverOptions(std::move(clangOptions),
                                                std::move(libFuzzerOptions)));
    assert(clangOptions.get() == nullptr);
    assert(libFuzzerOptions.get() == nullptr);
    solver.reset(new jfs::cxxfb::CXXFuzzingSolver(std::move(solverOptions),
                                                  std::move(wdm), ctx));
    assert(wdm.get() == nullptr);
    assert(solverOptions.get() == nullptr);
    break;
  }
  default:
    llvm_unreachable("unknown solver backend");
  }

  // HACK: This is a global so `handleInterrupt()` can call it.
  cancelFn = [&solver, &pm, &ctx]() {
    // Actions to perform if cancellation is requested
    IF_VERB(ctx, ctx.getDebugStream() << "(interrupted)\n");
    pm.cancel();
    solver->cancel();
  };

  llvm::sys::SetInterruptFunction(handleInterrupt);

  // Apply timeout
  jfs::support::ScopedTimer timer(MaxTime, cancelFn);

  // Run standard transformations
  AddStandardPasses(pm);
  pm.run(*query);
  if (Verbosity > 10)
    ctx.getDebugStream() << *query;

  if (Verbosity > 0)
    ctx.getDebugStream() << "(using solver \"" << solver->getName() << "\")\n";

  auto response = solver->solve(*query, /*produceModel=*/false);
  llvm::outs() << SolverResponse::getSatString(response->sat) << "\n";
  return 0;
}
