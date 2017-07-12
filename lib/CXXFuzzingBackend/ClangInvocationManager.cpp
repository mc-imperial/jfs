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
#include "jfs/CXXFuzzingBackend/ClangInvocationManager.h"
#include "jfs/CXXFuzzingBackend/CXXProgram.h"
#include "jfs/CXXFuzzingBackend/ClangOptions.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Support/CancellableProcess.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/raw_ostream.h"
#include <atomic>
#include <string>
#include <vector>
namespace jfs {
namespace cxxfb {

using namespace jfs::core;
using namespace jfs::support;

class ClangInvocationManagerImpl : public jfs::support::ICancellable {
private:
  JFSContext& ctx;
  std::atomic<bool> cancelled;
  CancellableProcess proc;

public:
  ClangInvocationManagerImpl(JFSContext& ctx) : ctx(ctx), cancelled(false) {}

  void cancel() override {
    cancelled = true;
    // Cancel Clang invocation
    IF_VERB(ctx,
            ctx.getDebugStream() << "(ClangInvocationManager cancel called)\n");
    proc.cancel();
  }

  bool compile(const CXXProgram* program, llvm::StringRef sourceFile,
               llvm::StringRef outputFile, const ClangOptions* options,
               llvm::StringRef stdoutFile, llvm::StringRef stdErrFile) {
    // FIXME: Implement pipe building mode.
    assert(sourceFile.size() > 0 &&
           "Support for non sourceFile build not implemented");

#define CHECK_CANCELLED()                                                      \
  if (cancelled) {                                                             \
    IF_VERB(ctx,                                                               \
            ctx.getDebugStream() << "(ClangInvocationManager cancelled)\n");   \
    return false;                                                              \
  }
    // Cancelation point
    CHECK_CANCELLED();

    // Write source file to disk
    std::error_code ec;
    llvm::raw_fd_ostream sourceStream(sourceFile, ec,
                                      llvm::sys::fs::OpenFlags::F_Excl);
    if (ec) {
      // Failed to open file for writing
      std::string underlyingString;
      llvm::raw_string_ostream ss(underlyingString);
      ss << "Failed to open " << sourceFile << " for writing because "
         << ec.message();
      ss.flush();
      ctx.raiseFatalError(underlyingString);
    }
    // FIXME: We need to be able to cancel writing to the file.
    program->print(sourceStream);
    assert(!(sourceStream.has_error()));
    sourceStream.close();

    CHECK_CANCELLED();

    // Invoke Clang

    // Build up command line arguments
    std::vector<const char*> cmdLineArgs;
    // arg0 should be the program name itself
    cmdLineArgs.push_back(options->pathToBinary.c_str());

    // Set C++ standard
    cmdLineArgs.push_back("-std=c++11");

    // Include path
    cmdLineArgs.push_back("-I");
    cmdLineArgs.push_back(options->pathToRuntimeIncludeDir.c_str());

    // Optimization level
    switch (options->optimizationLevel) {
    case ClangOptions::OptimizationLevel::O0:
      cmdLineArgs.push_back("-O0");
      break;
    case ClangOptions::OptimizationLevel::O1:
      cmdLineArgs.push_back("-O1");
      break;
    case ClangOptions::OptimizationLevel::O2:
      cmdLineArgs.push_back("-O2");
      break;
    case ClangOptions::OptimizationLevel::O3:
      cmdLineArgs.push_back("-O3");
      break;
    default:
      llvm_unreachable("Unhandled optimization level");
    }

    // Debug symbols
    if (options->debugSymbols) {
      cmdLineArgs.push_back("-g");
    }

    // TODO: Do we actually need this?
    cmdLineArgs.push_back("-fno-omit-frame-pointer");

    // ASan
    if (options->useASan) {
      cmdLineArgs.push_back("-fsanitize=address");
    }

    // UBSan
    if (options->useUBSan) {
      cmdLineArgs.push_back("-fsanitize=undefined");
    }
    // SanitizerCoverage options
    assert(options->sanitizerCoverageOptions.size() > 0);
    for (const auto& sanitizerCovOpt : options->sanitizerCoverageOptions) {
      switch (sanitizerCovOpt) {
      case ClangOptions::SanitizerCoverageTy::TRACE_PC_GUARD:
        cmdLineArgs.push_back("-fsanitize-coverage=trace-pc-guard");
        break;
      case ClangOptions::SanitizerCoverageTy::TRACE_CMP:
        cmdLineArgs.push_back("-fsanitize-coverage=trace-cmp");
        break;
      default:
        llvm_unreachable("Unhandled SanitizerCoverageTy");
      }
    }

    // JFS runtime asserts
    if (options->useJFSRuntimeAsserts) {
      cmdLineArgs.push_back("-DENABLE_JFS_RUNTIME_ASSERTS");
    }

    // Source file to compile
    cmdLineArgs.push_back(sourceFile.data());

    // Link against LibFuzzer
    cmdLineArgs.push_back(options->pathToLibFuzzerLib.c_str());

    // Set output path
    cmdLineArgs.push_back("-o");
    cmdLineArgs.push_back(outputFile.data());

    if (ctx.getVerbosity() > 0) {
      ctx.getDebugStream() << "(ClangInvocationManager \n [";
      for (const auto& arg : cmdLineArgs) {
        ctx.getDebugStream() << "\"" << arg << "\", ";
      }
      ctx.getDebugStream() << "]\n)\n";
    }

    // Null terminates args
    cmdLineArgs.push_back(nullptr);

    CHECK_CANCELLED();
    std::vector<llvm::StringRef> redirects;
    if (stdoutFile.size() > 0 || stdErrFile.size() > 0) {
      // Redirect stdin
      redirects.push_back("");         // STDIN goes to /dev/null
      redirects.push_back(stdoutFile); // STDOUT
      redirects.push_back(stdErrFile); // STDERR
    }
    int exitCode = proc.execute(
        /*program=*/options->pathToBinary,
        /*args=*/cmdLineArgs,
        /*redirects=*/redirects);

    if (exitCode == 0) {
      // Success
      return true;
    }
    if (exitCode == -2) {
      // Cancelled
      return false;
    }
    std::string underlyingString;
    llvm::raw_string_ostream ss(underlyingString);
    ss << "Clang invocation has exit code " << exitCode;
    ss.flush();
    ctx.raiseError(underlyingString);
    return false;
  }
};

ClangInvocationManager::ClangInvocationManager(JFSContext& ctx)
    : impl(new ClangInvocationManagerImpl(ctx)) {}

ClangInvocationManager::~ClangInvocationManager() {}

void ClangInvocationManager::cancel() { impl->cancel(); }

bool ClangInvocationManager::compile(const CXXProgram* program,
                                     llvm::StringRef sourceFile,
                                     llvm::StringRef outputFile,
                                     const ClangOptions* options,
                                     llvm::StringRef stdOutFile,
                                     llvm::StringRef stdErrFile) {
  return impl->compile(program, sourceFile, outputFile, options, stdOutFile,
                       stdErrFile);
}
}
}
