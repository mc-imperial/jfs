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
#include "jfs/FuzzingCommon/LibFuzzerInvocationManager.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/JFSTimerMacros.h"
#include "jfs/Support/CancellableProcess.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"
#include <atomic>
#include <vector>

namespace jfs {
namespace fuzzingCommon {

using namespace jfs::core;
using namespace jfs::support;

class LibFuzzerInvocationManagerImpl {
private:
  JFSContext& ctx;
  static const int targetFoundExitCode = 77;
  static const int unitTimeoutExitCode = 88;
  static const int singleRunTargetNotFoundExitCode = 0;
  std::atomic<bool> cancelled;
  CancellableProcess proc;

public:
  LibFuzzerInvocationManagerImpl(JFSContext& ctx)
      : ctx(ctx), cancelled(false) {}
  ~LibFuzzerInvocationManagerImpl() {}
  void cancel() {
    IF_VERB(ctx,
            ctx.getDebugStream()
                << "(LibFuzzerInvocationManager cancel called)\n");
    cancelled = true;
    proc.cancel();
  }
  std::unique_ptr<LibFuzzerResponse> fuzz(const LibFuzzerOptions* options,
                                          llvm::StringRef stdOutFile,
                                          llvm::StringRef stdErrFile) {
    // TODO: Assert paths exist
    std::vector<const char*> cmdLineArgs;

    // If previous steps failed to perform complete constant folding
    // then we might end up with an empty buffer. In that case we only
    // we only need to run the program once to determine sat/unsat.
    bool emptyBuffer = options->maxLength == 0;

    std::string underlyingString;
    llvm::raw_string_ostream ss(underlyingString);

#define SET_ARG(NAME, X)                                                       \
  ss << X;                                                                     \
  std::string NAME(ss.str());                                                  \
  cmdLineArgs.push_back(NAME.data());                                          \
  underlyingString.clear();

    // First arg must be fuzzing binary
    assert(llvm::sys::fs::exists(options->targetBinary));
    cmdLineArgs.push_back(options->targetBinary.data());

    SET_ARG(numberOfRunsArgs, "-runs=" << (emptyBuffer ? "1" : "-1"));

    // Seed
    SET_ARG(seedArg, "-seed=" << options->seed);

    // Mutation depth
    SET_ARG(mutationDepthArg, "-mutate_depth=" << options->mutationDepth);

    // Crossover
    SET_ARG(crossOverArg, "-cross_over=" << (options->crossOver ? "1" : "0"));

    // Max length
    SET_ARG(maxLengthArg, "-max_len=" << options->maxLength);

    // Use trace comparison
    SET_ARG(useCmpArg, "-use_cmp=" << (options->useCmp ? "1" : "0"));

    // Log stats
    SET_ARG(printFinalStats,
            "-print_final_stats=" << (options->printFinalStats ? "1" : "0"));

    // Reduce inputs
    SET_ARG(reduceInputs,
            "-reduce_inputs=" << (options->reduceInputs ? "1" : "0"));

    // Control whether LibFuzzer's default mutators resize input.
    // Generally resizing the inputs is not desirable.
    //
    // Disabling mutations that resize the input is highly experimental.
    SET_ARG(defaultMutationsResizeInput,
            "-default_mutators_resize_input="
                << (options->defaultMutationsResizeInput ? "1" : "0"));

    // handle SIGABRT
    SET_ARG(handleSIGABRTArg,
            "-handle_abrt=" << (options->handleSIGABRT ? "1" : "0"));

    // handle SIGBUS
    SET_ARG(handleSIGBUSArg,
            "-handle_bus=" << (options->handleSIGBUS ? "1" : "0"));

    // handle SIGFPE
    SET_ARG(handleSIGFPEArg,
            "-handle_fpe=" << (options->handleSIGFPE ? "1" : "0"));

    // handle SIGILL
    SET_ARG(handleSIGILLArg,
            "-handle_ill=" << (options->handleSIGILL ? "1" : "0"));

    // handle SIGINT
    SET_ARG(handleSIGIntArg,
            "-handle_int=" << (options->handleSIGINT ? "1" : "0"));

    // handle SIGSEGV
    SET_ARG(handleSIGSEGVArg,
            "-handle_segv=" << (options->handleSIGSEGV ? "1" : "0"));

    // handle SIGTERM
    SET_ARG(handleSIGTERMArg,
            "-handle_term=" << (options->handleSIGTERM ? "1" : "0"));

    // handle SIGXFSZ
    SET_ARG(handleSIGXFSZArg,
            "-handle_xfsz=" << (options->handleSIGXFSZ ? "1" : "0"));

    // Artifact dir
    // TODO: Use Twine?
    std::string artifactPathWithSlash(options->artifactDir);
    artifactPathWithSlash += "/";
    artifactPathWithSlash =
        llvm::sys::path::convert_to_slash(artifactPathWithSlash);
    assert(llvm::sys::fs::is_directory(artifactPathWithSlash));
    SET_ARG(artifactArg, "-artifact_prefix=" << artifactPathWithSlash);

    // Set exit codes. We use this to work out what the outcome was
    SET_ARG(errorExitCodeArg, "-error_exitcode=" << targetFoundExitCode);
    SET_ARG(unitTimeoutExitCodeArg,
            "-timeout_exitcode=" << unitTimeoutExitCode);

    // Corpus directory
    assert(llvm::sys::fs::is_directory(options->corpusDir));
    cmdLineArgs.push_back(options->corpusDir.data());

#undef SET_ARG
    if (ctx.getVerbosity() > 0) {
      ctx.getDebugStream() << "(LibFuzzerInvocationManager\n[";
      for (const auto& arg : cmdLineArgs) {
        ctx.getDebugStream() << "\"" << arg << "\", ";
      }
      ctx.getDebugStream() << "]\n)\n";
    }
    std::unique_ptr<LibFuzzerResponse> response(new LibFuzzerResponse());

    // cmdLineArgs must be null terminated
    cmdLineArgs.push_back(nullptr);

    // Redirects
    std::vector<llvm::StringRef> redirects;
    if (stdOutFile.size() > 0 || stdErrFile.size() > 0) {
      redirects.push_back("");         // STDIN goes to /dev/null
      redirects.push_back(stdOutFile); // STDOUT
      redirects.push_back(stdErrFile); // STDERR
    }

    // Set up environment variable to tell the program where to
    // log runtime statistics if required.
    const char** envp = nullptr;
    std::string jfsRuntimeEnv;
    if (options->jfsRuntimeLogFile.size() > 0) {
      jfsRuntimeEnv = "JFS_RUNTIME_LOG_PATH=";
      jfsRuntimeEnv += options->jfsRuntimeLogFile;
    }
    const char* envpLogging[] = {jfsRuntimeEnv.c_str(), nullptr};
    if (options->jfsRuntimeLogFile.size() > 0) {
      envp = envpLogging;
    }

    // Invoke Fuzzer
    int exitCode = proc.execute(/*program=*/options->targetBinary,
                                /*args=*/cmdLineArgs, /*redirects=*/redirects,
                                /*envp=*/envp);

    if (exitCode == -2) {
      response->outcome = LibFuzzerResponse::ResponseTy::CANCELLED;
      return response;
    }
    if (emptyBuffer && exitCode == singleRunTargetNotFoundExitCode) {
      response->outcome =
          LibFuzzerResponse::ResponseTy::SINGLE_RUN_TARGET_NOT_FOUND;
      return response;
    }
    if (exitCode != targetFoundExitCode) {
      ctx.getErrorStream() << "(error Unexpected exit code from LibFuzzer "
                           << exitCode << ")\n";
      response->outcome = LibFuzzerResponse::ResponseTy::UNKNOWN;
      return response;
    }

    // TODO: Populate response with input that caused the target to be found
    response->outcome = LibFuzzerResponse::ResponseTy::TARGET_FOUND;
    return response;
  }
};

// LibFuzzerResponse

LibFuzzerResponse::LibFuzzerResponse() : outcome(ResponseTy::UNKNOWN) {}
LibFuzzerResponse::~LibFuzzerResponse() {}

// LibFuzzerInvocationManager
LibFuzzerInvocationManager::LibFuzzerInvocationManager(JFSContext& ctx)
    : impl(new LibFuzzerInvocationManagerImpl(ctx)) {}

LibFuzzerInvocationManager::~LibFuzzerInvocationManager() {}

void LibFuzzerInvocationManager::cancel() { impl->cancel(); }

std::unique_ptr<LibFuzzerResponse>
LibFuzzerInvocationManager::fuzz(const LibFuzzerOptions* options,
                                 llvm::StringRef stdOutFile,
                                 llvm::StringRef stdErrFile) {
  return impl->fuzz(options, stdOutFile, stdErrFile);
}
}
}
