//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/CXXFuzzingBackend/CXXFuzzingSolver.h"
#include "jfs/CXXFuzzingBackend/CXXFuzzingSolverOptions.h"
#include "jfs/CXXFuzzingBackend/CXXProgram.h"
#include "jfs/CXXFuzzingBackend/CXXProgramBuilderPass.h"
#include "jfs/CXXFuzzingBackend/ClangInvocationManager.h"
#include "jfs/CXXFuzzingBackend/ClangOptions.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/JFSTimerMacros.h"
#include "jfs/FuzzingCommon/JFSRuntimeFuzzingStat.h"
#include "jfs/FuzzingCommon/LibFuzzerInvocationManager.h"
#include "jfs/FuzzingCommon/SortConformanceCheckPass.h"
#include "jfs/FuzzingCommon/WorkingDirectoryManager.h"
#include "jfs/Transform/QueryPass.h"
#include "jfs/Transform/QueryPassManager.h"
#include "llvm/Support/CommandLine.h"
#include <algorithm>
#include <atomic>
#include <mutex>
#include <unordered_set>

using namespace jfs::core;
using namespace jfs::fuzzingCommon;
using namespace jfs::transform;

namespace {
// FIXME: Should use an OptionCategory but
// we shouldn't pull in `jfs::cxxfb::cl::CommandLineCategory` because
// that defeats the purpose of having the separate libraries. So instead
// just hide the option by default. It's only meant for internal testing
// anyway.
llvm::cl::opt<bool> DebugStopAfterCompilation(
    "debug-stop-after-compile", llvm::cl::init(false),
    llvm::cl::desc("Stop CXXFuzzingSolver after clang compilation"),
    llvm::cl::Hidden);
}

namespace jfs {
namespace cxxfb {

class CXXFuzzingSolverResponse : public SolverResponse {
public:
  CXXFuzzingSolverResponse(SolverResponse::SolverSatisfiability sat)
      : SolverResponse(sat) {}
  std::shared_ptr<Model> getModel() override {
    // TODO: Figure out how to do model generation
    return nullptr;
  }
};

class CXXFuzzingSolverImpl {
  std::mutex cancellablePassesMutex; // protects `cancellablePasses`
  std::unordered_set<jfs::transform::QueryPass*> cancellablePasses;
  std::atomic<bool> cancelled;
  JFSContext& ctx;
  // Raw pointer because we don't own the storage.
  CXXFuzzingSolverOptions* options;
  ClangInvocationManager cim;
  LibFuzzerInvocationManager lim;
  WorkingDirectoryManager* wdm;

public:
  friend class CXXFuzzingSolver;
  CXXFuzzingSolverImpl(JFSContext& ctx, CXXFuzzingSolverOptions* options,
                       WorkingDirectoryManager* wdm)
      : cancelled(false), ctx(ctx), options(options), cim(ctx), lim(ctx),
        wdm(wdm) {
    assert(this->wdm != nullptr);
    assert(this->options != nullptr);
    // Check paths
    bool clangPathsOkay = options->getClangOptions()->checkPaths(ctx);
    if (!clangPathsOkay) {
      ctx.raiseFatalError("One or more Clang paths do not exist");
    }
  }
  ~CXXFuzzingSolverImpl() {}

  llvm::StringRef getName() { return "CXXFuzzingSolver"; }
  void cancel() {
    cancelled = true;
    // Cancel any active passes
    {
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      for (const auto& pass : cancellablePasses) {
        pass->cancel();
      }
    }
    // Cancel active Clang invocation
    cim.cancel();
    // Cancel active LibFuzzer invocation
    lim.cancel();
  }

  // FIXME: Should be const Query.
  bool sortsAreSupported(Query& q) {
    JFSContext &ctx = q.getContext();
    auto p = std::make_shared<SortConformanceCheckPass>([&ctx](Z3SortHandle s) {
      switch (s.getKind()) {
      case Z3_BOOL_SORT: {
        return true;
      }
      case Z3_BV_SORT: {
        unsigned width = s.getBitVectorWidth();
        if (width <= 64) {
          return true;
        }
        // Too wide
        IF_VERB(ctx,
                ctx.getWarningStream()
                    << "(BitVector width " << width << " not supported)\n");
        return false;
      }
      case Z3_FLOATING_POINT_SORT: {
        unsigned ebits = s.getFloatingPointExponentBitWidth();
        unsigned sbits = s.getFloatingPointSignificandBitWidth();
        if (ebits == 8 && sbits == 24) {
          // Float32
          return true;
        } else if (ebits == 11 && sbits == 53) {
          // Float64
          return true;
        }
        return false;
      }
      case Z3_ROUNDING_MODE_SORT:
        return true;
      default: {
        // Sort not supported
        IF_VERB(ctx,
                ctx.getWarningStream()
                    << "(Sort \"" << s.toStr() << "\" not supported)\n");
        return false;
      }
      }
    });

    QueryPassManager pm;
    {
      // Make the pass cancellable
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      cancellablePasses.insert(p.get());
      pm.add(p);
    }

    pm.run(q);

    {
      // The pass is done remove it from set of cancellable passes
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      cancellablePasses.erase(p.get());
    }
    return p->predicateAlwaysHeld();
  }

  std::unique_ptr<jfs::core::SolverResponse>
  fuzz(jfs::core::Query &q, bool produceModel,
       std::shared_ptr<FuzzingAnalysisInfo> info) {
    assert(ctx == q.getContext());
    if (produceModel) {
      ctx.getErrorStream() << "(error model generation not supported)\n";
      return nullptr;
    }
#define CHECK_CANCELLED()                                                      \
  if (cancelled) {                                                             \
    IF_VERB(ctx, ctx.getDebugStream() << "(" << getName() << " cancelled)\n"); \
    return std::unique_ptr<SolverResponse>(                                    \
        new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));                \
  }

    // Check types are supported
    if (!sortsAreSupported(q)) {
      IF_VERB(ctx, ctx.getDebugStream() << "(unsupported sorts)\n");
      return std::unique_ptr<SolverResponse>(
          new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));
    }

    // Cancellation point
    CHECK_CANCELLED();

    // Generate program
    QueryPassManager pm;
    auto pbp = std::make_shared<CXXProgramBuilderPass>(
        info, options->getCXXProgramBuilderOptions(), ctx);

    {
      // Make the pass cancellable
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      cancellablePasses.insert(pbp.get());
      pm.add(pbp);
    }
    pm.run(q);
    {
      // Pass is done. Remove from the set of cancellable passes
      std::lock_guard<std::mutex> lock(cancellablePassesMutex);
      cancellablePasses.insert(pbp.get());
    }

    // Cancellation point
    CHECK_CANCELLED();

    // Build program
    // FIXME: We should teach ClangInvocationManager to pipe the program
    // directly
    // to Clang so we don't need to write it disk and then immediatly read it
    // back.
    std::string outputFilePath;
    {
      JFS_SM_TIMER(compile, ctx);
      std::string sourceFilePath = wdm->getPathToFileInDirectory("program.cpp");
      outputFilePath = wdm->getPathToFileInDirectory("fuzzer");
      std::string clangStdOutFile;
      std::string clangStdErrFile;
      if (options->redirectClangOutput) {
        // When being quiet redirect to files
        clangStdOutFile = wdm->getPathToFileInDirectory("clang.stdout.txt");
        clangStdErrFile = wdm->getPathToFileInDirectory("clang.stderr.txt");
      }
      bool compileSuccess = cim.compile(
          /*program=*/pbp->getProgram().get(), /*sourceFile=*/sourceFilePath,
          /*outputFile=*/outputFilePath,
          /*clangOptions=*/options->getClangOptions(),
          /*stdOutFile=*/clangStdOutFile,
          /*stdErrFile=*/clangStdErrFile);
      if (!compileSuccess) {
        return std::unique_ptr<SolverResponse>(
            new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));
      }
    }
    // Cancellation point
    CHECK_CANCELLED();

    if (DebugStopAfterCompilation) {
      // For debugging it can be useful to check that JFS can successfully
      // run and compile the fuzzing program without actually fuzzing.
      IF_VERB(ctx, ctx.getDebugStream() << "(DebugStopAfterCompilation)\n");
      return std::unique_ptr<SolverResponse>(
          new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));
    }

    // Set LibFuzzer options
    JFS_SM_TIMER(fuzz, ctx);
    LibFuzzerOptions* lfo = options->getLibFuzzerOptions();
    // FIXME: We've already computed this earlier so we should cache it
    // somewhere.
    lfo->maxLength =
        (info->freeVariableAssignment->bufferAssignment->computeWidth() + 7) /
        8;
    lfo->targetBinary = outputFilePath;
    std::string corpusDir = wdm->makeNewDirectoryInDirectory("corpus");
    lfo->corpusDir = corpusDir;
    std::string artifactDir = wdm->makeNewDirectoryInDirectory("artifacts");
    lfo->artifactDir = artifactDir;
    std::string libFuzzerStdOutFile;
    std::string libFuzzerStdErrFile;
    lfo->useCmp = false;
    // FIXME: This is O(N). We should probably change sanitizerCoverageOptions
    // to be a set.
    if (std::find(options->getClangOptions()->sanitizerCoverageOptions.begin(),
                  options->getClangOptions()->sanitizerCoverageOptions.end(),
                  ClangOptions::SanitizerCoverageTy::TRACE_CMP) !=
        options->getClangOptions()->sanitizerCoverageOptions.end()) {
      lfo->useCmp = true;
    }
    // FIXME: The fact that our fuzzing target is `abort()` is really fragile.
    lfo->handleSIGABRT =
        true; // Our target is an `abort()` so we want to catch this.
    lfo->handleSIGBUS = false; // We don't want to confuse this with the target.
    lfo->handleSIGFPE = false; // We don't want to confuse this with the target.
    lfo->handleSIGILL = false; // We don't want to confuse this with the target.
    lfo->handleSIGINT =
        true; // This doesn't trigger LibFuzzer's error handler so this is fine.
    lfo->handleSIGSEGV =
        false; // We don't want to confuse this with the target.
    lfo->handleSIGTERM =
        true; // This doesn't trigger LibFuzzer's error handler so this is fine.
    lfo->handleSIGXFSZ =
        true; // This doesn't trigger LibFuzzer's error handler so this is fine.

    if (options->redirectLibFuzzerOutput) {
      // When being quiet redirect to files
      libFuzzerStdOutFile =
          wdm->getPathToFileInDirectory("libfuzzer.stdout.txt");
      libFuzzerStdErrFile =
          wdm->getPathToFileInDirectory("libfuzzer.stderr.txt");
    }

    if (pbp->getProgram()->getRecordsRuntimeStats()) {
      // Tell LibFuzzerInvocationManager that it needs to log runtime statistics
      lfo->jfsRuntimeLogFile =
          wdm->getPathToFileInDirectory("jfs_runtime_stats.yml");
    }

    // Fuzz
    auto fuzzingResponse =
        lim.fuzz(lfo, libFuzzerStdOutFile, libFuzzerStdErrFile);

    // Get runtime stastics
    std::unique_ptr<JFSRuntimeFuzzingStat> rfs;
    if (lfo->jfsRuntimeLogFile.size() > 0) {
      rfs = JFSRuntimeFuzzingStat::LoadFromYAML(lfo->jfsRuntimeLogFile,
                                                "runtime_fuzzing_stats", ctx);
      if (rfs != nullptr && ctx.getStats() != nullptr) {
        ctx.getStats()->append(std::move(rfs));
      } else {
        ctx.getWarningStream()
            << "(warning Failed to retrive runtime fuzzing stats)\n";
      }
    }

    switch (fuzzingResponse->outcome) {
    case LibFuzzerResponse::ResponseTy::UNKNOWN:
    case LibFuzzerResponse::ResponseTy::CANCELLED: {
      return std::unique_ptr<SolverResponse>(
          new CXXFuzzingSolverResponse(SolverResponse::UNKNOWN));
    }
    case LibFuzzerResponse::ResponseTy::SINGLE_RUN_TARGET_NOT_FOUND: {
      // Special case where the fuzzer only does a single run due to
      // empty buffer.
      return std::unique_ptr<SolverResponse>(
          new CXXFuzzingSolverResponse(SolverResponse::UNSAT));
    }
    case LibFuzzerResponse::ResponseTy::TARGET_FOUND: {
      // Solution found
      // TODO: Handle setting up model if its needed.
      return std::unique_ptr<SolverResponse>(
          new CXXFuzzingSolverResponse(SolverResponse::SAT));
    }
    default:
      llvm_unreachable("Unhandled LibFuzzerResponse");
    }
    return nullptr;
  }
};

CXXFuzzingSolver::CXXFuzzingSolver(
    std::unique_ptr<CXXFuzzingSolverOptions> options,
    std::unique_ptr<WorkingDirectoryManager> wdm, JFSContext& ctx)
    : jfs::fuzzingCommon::FuzzingSolver(std::move(options), std::move(wdm),
                                        ctx),
      impl(new CXXFuzzingSolverImpl(
          ctx, static_cast<CXXFuzzingSolverOptions*>(this->options.get()),
          this->wdm.get())) {}

CXXFuzzingSolver::~CXXFuzzingSolver() {}

std::unique_ptr<jfs::core::SolverResponse>
CXXFuzzingSolver::fuzz(jfs::core::Query &q, bool produceModel,
                       std::shared_ptr<FuzzingAnalysisInfo> info) {
  return impl->fuzz(q, produceModel, info);
}

llvm::StringRef CXXFuzzingSolver::getName() const { return "CXXFuzzingSolver"; }

void CXXFuzzingSolver::cancel() {
  // Call parent
  FuzzingSolver::cancel();
  // Notify implementation
  impl->cancel();
}
}
}
