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
#include "jfs/FuzzingCommon/LibFuzzerInvocationManager.h"
#include "jfs/Core/IfVerbose.h"
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

  void setupSeeds(const LibFuzzerOptions* options) {
    if (options->addAllZeroMaxLengthSeed) {
      IF_VERB(ctx,
              ctx.getDebugStream()
                  << "(LibFuzzerInvocationManager Adding AllZero seed)\n");
      // Create a seed in the corpus directory that's the maximum size
      // all filled with zeros.
      // FIXME: We should probably just teach LibFuzzer about this rather than
      // using this hack.
      assert(options->maxLength > 0);
      std::unique_ptr<uint8_t> buffer((uint8_t*)malloc(options->maxLength));
      memset(buffer.get(), 0, options->maxLength);
      llvm::SmallVector<char, 256> mutablePath(options->corpusDir.begin(),
                                               options->corpusDir.end());
      llvm::sys::path::append(mutablePath, "zeroSeed");
      mutablePath.push_back('\0');
      llvm::StringRef zeroSeedFilePath(mutablePath.data(), mutablePath.size());
      std::error_code ec;
      llvm::raw_fd_ostream zeroSeedFileStream(zeroSeedFilePath, ec,
                                              llvm::sys::fs::F_Excl);
      if (ec) {
        std::string underlyingString;
        llvm::raw_string_ostream ss(underlyingString);
        ss << "Failed to open " << zeroSeedFilePath << " for writing because "
           << ec.message();
        ss.flush();
        ctx.raiseFatalError(underlyingString);
      }
      zeroSeedFileStream.write(reinterpret_cast<const char*>(buffer.get()),
                               options->maxLength);
      assert(!zeroSeedFileStream.has_error());
      zeroSeedFileStream.close();
      IF_VERB(
          ctx,
          ctx.getDebugStream()
              << "(LibFuzzerInvocationManager Finished Adding AllZero seed)\n");
    }
  }
  std::unique_ptr<LibFuzzerResponse> fuzz(const LibFuzzerOptions* options,
                                          llvm::StringRef stdOutFile,
                                          llvm::StringRef stdErrFile) {
    // TODO: Assert paths exist
    std::vector<const char*> cmdLineArgs;

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

    // Setup the seeds
    setupSeeds(options);

    // Invoke Fuzzer
    int exitCode = proc.execute(/*program=*/options->targetBinary,
                                /*args=*/cmdLineArgs, /*redirects=*/redirects);

    if (exitCode == -2) {
      response->outcome = LibFuzzerResponse::ResponseTy::CANCELLED;
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
