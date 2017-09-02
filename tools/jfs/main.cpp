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
#include "jfs/Core/JFSTimerMacros.h"
#include "jfs/Core/SMTLIB2Parser.h"
#include "jfs/Core/ScopedJFSContextErrorHandler.h"
#include "jfs/Core/ToolErrorHandler.h"
#include "jfs/FuzzingCommon/CmdLine/LibFuzzerOptionsBuilder.h"
#include "jfs/FuzzingCommon/DummyFuzzingSolver.h"
#include "jfs/Support/ErrorMessages.h"
#include "jfs/Support/ScopedTimer.h"
#include "jfs/Support/StatisticsManager.h"
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

llvm::cl::opt<std::string>
    StatsFilename("stats-file",
                  llvm::cl::desc("Location to write stats file. `-` writes to "
                                 "stdout. (default don't write file)"),
                  llvm::cl::init(""));

// FIXME: Remove this when we provide a cleaner way to specify passes.
llvm::cl::opt<bool> DisableStandardPasses(
    "disable-standard-passes", llvm::cl::init(false),
    llvm::cl::desc("Do not run standard passes (default false)"),
    llvm::cl::Hidden);

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

std::unique_ptr<jfs::fuzzingCommon::WorkingDirectoryManager>
makeWorkingDirectory(JFSContext& ctx) {
  if (OutputDirectory.size() > 0) {
    // Use user specified path for working directory
    return jfs::fuzzingCommon::WorkingDirectoryManager::makeAtPath(
        OutputDirectory, ctx, !KeepOutputDirectory);
  }
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
  return jfs::fuzzingCommon::WorkingDirectoryManager::makeInDirectory(
      /*directory=*/currentDirAsStringRef, /*prefix=*/prefix, ctx,
      !KeepOutputDirectory);
}

std::unique_ptr<Solver>
makeSolver(JFSContext& ctx,
           std::unique_ptr<jfs::fuzzingCommon::WorkingDirectoryManager> wdm,
           llvm::StringRef pathToExecutable) {
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
    auto clangOptions =
        jfs::cxxfb::cl::buildClangOptionsFromCmdLine(pathToExecutable);
    IF_VERB(ctx, clangOptions->print(ctx.getDebugStream()));

    auto libFuzzerOptions =
        jfs::fuzzingCommon::cl::buildLibFuzzerOptionsFromCmdLine();

    std::unique_ptr<jfs::cxxfb::CXXFuzzingSolverOptions> solverOptions(
        new jfs::cxxfb::CXXFuzzingSolverOptions(std::move(clangOptions),
                                                std::move(libFuzzerOptions)));
    solver.reset(new jfs::cxxfb::CXXFuzzingSolver(std::move(solverOptions),
                                                  std::move(wdm), ctx));
    break;
  }
  default:
    llvm_unreachable("unknown solver backend");
  }
  return solver;
}

std::function<void(void)> cancelFn;

void handleInterrupt() {
  if (cancelFn)
    cancelFn();
}

int main(int argc, char** argv) {
  llvm::cl::SetVersionPrinter(printVersion);
  llvm::cl::ParseCommandLineOptions(argc, argv);

  // Create context
  JFSContextConfig ctxCfg;
  ctxCfg.verbosity = Verbosity;
  ctxCfg.gathericStatistics = (StatsFilename != "");

  JFSContext ctx(ctxCfg);
  ToolErrorHandler toolHandler(/*ignoreCanceled*/ true);
  ScopedJFSContextErrorHandler errorHandler(ctx, &toolHandler);

  std::unique_ptr<llvm::raw_fd_ostream> sfStorage;
  llvm::raw_ostream* sf = nullptr;
  if (StatsFilename != "") {
    // Open stats file early so we fail early if it can't be opened
    std::error_code ec;
    if (StatsFilename == "-") {
      // We have to handle stdout specially. We use `outs()` which means
      // we can't also create a separate llvm::raw_fd_ostream() otherwise
      // we'll close the file twice.
      sf = &(llvm::outs());
    } else {
      sfStorage.reset(
          new llvm::raw_fd_ostream(StatsFilename, ec, llvm::sys::fs::F_Excl));
      if (ec) {
        ctx.getErrorStream()
            << jfs::support::getMessageForFailedOpenFileForWriting(
                   StatsFilename, ec);
        return 1;
      }
      sf = sfStorage.get();
    }
  }

  // Create parser
  SMTLIB2Parser parser(ctx);

  // Create pass manager
  QueryPassManager pm;

  // Create working directory and solver
  std::string pathToExecutable = llvm::sys::fs::getMainExecutable(
      argv[0], reinterpret_cast<void*>(reinterpret_cast<intptr_t>(main)));
  std::unique_ptr<Solver> solver(
      makeSolver(ctx, makeWorkingDirectory(ctx), pathToExecutable));

  // Now set up cancel/interrupt handlers. We do this now so that all the
  // objects we need to interact with at cancellation time can be captured in
  // lambda.
  std::atomic<bool> parsingDone(false);
  cancelFn = [&parsingDone, &solver, &pm, &ctx]() {
    // Actions to perform if cancellation is requested
    IF_VERB(ctx, ctx.getDebugStream() << "(cancelling)\n");
    if (!parsingDone) {
      // HACK: We can't interrupt parsing so we have to just
      // do a best effort here and try to exit cleanly.
      // FIXME: We need to clean up the empty working directory.
      llvm::outs() << "unknown\n";
      exit(0);
    }
    pm.cancel();
    solver->cancel();
  };

  // Setup interrupt handler. This basically just calls
  // cancelFn.
  llvm::sys::SetInterruptFunction(handleInterrupt);

  // Apply timeout
  jfs::support::ScopedTimer timer(MaxTime, [&ctx]() {
    IF_VERB(ctx, ctx.getDebugStream() << "(timeout)\n");
    cancelFn();
  });

  // Parse query
  std::shared_ptr<Query> query;
  IF_VERB(ctx, ctx.getDebugStream() << "(Parser starting)\n");
  {
    JFS_SM_TIMER(parse_query, ctx);
    auto bufferOrError = llvm::MemoryBuffer::getFileOrSTDIN(InputFilename);
    if (auto error = bufferOrError.getError()) {
      ctx.getErrorStream() << jfs::support::getMessageForFailedOpenFileOrSTDIN(
          InputFilename, error);
      return 1;
    }
    auto buffer(std::move(bufferOrError.get()));
    // NOTE: the ToolErrorHandler will deal with parsing errors.
    query = parser.parseMemoryBuffer(std::move(buffer));
  }
  parsingDone = true;
  IF_VERB(ctx, ctx.getDebugStream() << "(Parser finished)\n");
  if (Verbosity > 10)
    ctx.getDebugStream() << *query;

  // FIXME: We need a better way to control this on the command line, like
  // we can do with `jfs-opt`.
  // Run standard transformations
  if (!DisableStandardPasses) {
    AddStandardPasses(pm);
    pm.run(*query);
    if (Verbosity > 10)
      ctx.getDebugStream() << *query;
  }

  if (Verbosity > 0)
    ctx.getDebugStream() << "(using solver \"" << solver->getName() << "\")\n";

  auto response = solver->solve(*query, /*produceModel=*/false);
  llvm::outs() << SolverResponse::getSatString(response->sat) << "\n";

  // Write statistics out
  if (StatsFilename != "") {
    assert(sf != nullptr);
    if (Verbosity > 0) {
      ctx.getDebugStream() << "(writing stats to \"" << StatsFilename
                           << "\")\n";
    }
    ctx.getStats()->printYAML(*sf);
    sf->flush();
  }
  return 0;
}
