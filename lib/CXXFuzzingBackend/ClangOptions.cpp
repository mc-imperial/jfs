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
#include "jfs/CXXFuzzingBackend/ClangOptions.h"
#include "jfs/Core/IfVerbose.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Twine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
namespace jfs {
namespace cxxfb {

ClangOptions::ClangOptions()
    : pathToBinary(""), pathToRuntimeDir(""), pathToRuntimeIncludeDir(""),
      pathToLibFuzzerLib(""), optimizationLevel(OptimizationLevel::O0),
      debugSymbols(false), useASan(false), useUBSan(false),
      useJFSRuntimeAsserts(false) {}

bool ClangOptions::checkPaths(jfs::core::JFSContext& ctx) const {
  bool ok = true;
  if (!llvm::sys::fs::exists(pathToBinary)) {
    IF_VERB(ctx,
            ctx.getWarningStream() << "(warning path to clang \""
                                   << pathToBinary << "\" does not exist)\n");
    ok = false;
  }

  if (!llvm::sys::fs::exists(pathToLibFuzzerLib)) {
    IF_VERB(ctx,
            ctx.getWarningStream()
                << "(warning path to LibFuzzer library \"" << pathToLibFuzzerLib
                << "\" does not exist)\n");
    ok = false;
  }
  bool isDirectory = llvm::sys::fs::is_directory(pathToRuntimeIncludeDir);
  if (!isDirectory) {
    IF_VERB(ctx,
            ctx.getWarningStream()
                << "(warning path to runtime include directory \""
                << pathToRuntimeIncludeDir << "\" does not exist)\n");
    ok = false;
  }
  isDirectory = llvm::sys::fs::is_directory(pathToRuntimeDir);
  if (!isDirectory) {
    IF_VERB(ctx,
            ctx.getWarningStream()
                << "(warning path to runtime directory \"" << pathToRuntimeDir
                << "\" does not exist)\n");
    ok = false;
  }
  return ok;
}

ClangOptions::ClangOptions(llvm::StringRef pathToExecutable,
                           LibFuzzerBuildType lfbt)
    : ClangOptions() {
  // Try to infer paths
  assert(pathToExecutable.data() != nullptr);
  assert(pathToExecutable.size() > 0);
  assert(llvm::sys::path::is_absolute(llvm::Twine(pathToExecutable)));
  llvm::SmallVector<char, 256> mutablePath(pathToExecutable.begin(),
                                           pathToExecutable.end());
  // Remove "/bin/jfs"
  llvm::sys::path::remove_filename(mutablePath);
  llvm::sys::path::remove_filename(mutablePath);

  // Set path to runtime directory
  llvm::sys::path::append(mutablePath, "runtime");
  pathToRuntimeDir = std::string(mutablePath.data(), mutablePath.size());

  // Set path to Clang
  llvm::sys::path::append(mutablePath, "bin", "clang++");
  pathToBinary = std::string(mutablePath.data(), mutablePath.size());

  // Remove "bin/clang++"
  llvm::sys::path::remove_filename(mutablePath);
  llvm::sys::path::remove_filename(mutablePath);

  // Set path to runtime include directory
  llvm::sys::path::append(mutablePath, "include");
  pathToRuntimeIncludeDir = std::string(mutablePath.data(), mutablePath.size());
  // Remove "include"
  llvm::sys::path::remove_filename(mutablePath);

  // Set path to libFuzzer library
  switch (lfbt) {
  case LibFuzzerBuildType::REL_WITH_DEB_INFO:
    llvm::sys::path::append(mutablePath, "LibFuzzer_RelWithDebInfo");
    break;
  default:
    llvm_unreachable("Unhandled LibFuzzer build type");
  }
  // FIXME: This is linux specific
  llvm::sys::path::append(mutablePath, "Fuzzer", "libLLVMFuzzer.a");
  pathToLibFuzzerLib = std::string(mutablePath.data(), mutablePath.size());
}

void ClangOptions::appendSanitizerCoverageOption(SanitizerCoverageTy opt) {
  sanitizerCoverageOptions.push_back(opt);
}

void ClangOptions::dump() const { print(llvm::errs()); }

void ClangOptions::print(llvm::raw_ostream& os) const {
  os << "pathToBinary: \"" << pathToBinary << "\"\n";
  os << "pathToRuntimeIncludeDir: \"" << pathToRuntimeIncludeDir << "\"\n";
  os << "pathToLibFuzzerLib: \"" << pathToLibFuzzerLib << "\"\n";
  os << "optimizationLevel: ";
  switch (optimizationLevel) {
#define HANDLE_LEVEL(X)                                                        \
  case OptimizationLevel::X:                                                   \
    os << #X << "\n";                                                          \
    break;
    HANDLE_LEVEL(O0);
    HANDLE_LEVEL(O1);
    HANDLE_LEVEL(O2);
    HANDLE_LEVEL(O3);
#undef HANDLE_LEVEL
  }
  os << "debug symbols:" << (debugSymbols ? "true" : "false") << "\n";
  os << "useASan: " << (useASan ? "true" : "false") << "\n";
  os << "useUBSan: " << (useUBSan ? "true" : "false") << "\n";
  os << "sanitizerCoverageOptions:";
  for (const auto& opt : sanitizerCoverageOptions) {
    switch (opt) {
    case SanitizerCoverageTy::TRACE_PC_GUARD:
      os << " TRACE_PC_GUARD";
      break;
    case SanitizerCoverageTy::TRACE_CMP:
      os << " TRACE_CMP";
      break;
    default:
      llvm_unreachable("Unhandled sanitizer coverage option");
    }
  }
  os << "\n";
}
}
}
