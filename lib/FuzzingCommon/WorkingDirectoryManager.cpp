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
#include "jfs/FuzzingCommon/WorkingDirectoryManager.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Support/FileUtils.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"
#include <assert.h>

namespace jfs {
namespace fuzzingCommon {

WorkingDirectoryManager::WorkingDirectoryManager(llvm::StringRef path,
                                                 jfs::core::JFSContext& ctx,
                                                 bool deleteOnDestruction)
    : path(path.str()), ctx(ctx), deleteOnDestruction(deleteOnDestruction) {

  assert(llvm::sys::path::is_absolute(this->path));
  assert(llvm::sys::fs::is_directory(this->path));
  // TODO: Assert directory is empty
  IF_VERB(ctx,
          ctx.getDebugStream()
              << "(WorkingDirectoryManager \"" << this->path
              << "\", deleteOnDestruction: " << deleteOnDestruction << ")\n");
}

WorkingDirectoryManager::~WorkingDirectoryManager() {
  if (!deleteOnDestruction)
    return;
  IF_VERB(ctx,
          ctx.getDebugStream() << "(Removing directory \"" << path << "\")\n");
  auto error =
      jfs::support::recursive_remove(path, /*IgnoreNonExisting=*/false);
  if (error) {
    std::string msg;
    llvm::raw_string_ostream ss(msg);
    ss << "Failed to remove directory " << path << " because "
       << error.message();
    ss.flush();
    ctx.raiseError(msg);
  }
}

std::unique_ptr<WorkingDirectoryManager>
WorkingDirectoryManager::makeAtPath(llvm::StringRef path,
                                    jfs::core::JFSContext& ctx,
                                    bool deleteOnDestruction) {

  std::unique_ptr<WorkingDirectoryManager> toReturn(nullptr);
  llvm::SmallVector<char, 256> mutablePath(path.begin(), path.end());
  if (auto error = llvm::sys::fs::make_absolute(mutablePath)) {
    std::string msg;
    llvm::raw_string_ostream ss(msg);
    ss << "Failed to make " << path << " absolute";
    ss.flush();
    ctx.raiseFatalError(msg);
  }
  if (auto error = llvm::sys::fs::create_directory(mutablePath,
                                                   /*IgnoreExisting=*/false)) {
    std::string msg;
    llvm::raw_string_ostream ss(msg);
    ss << "Failed to make " << path << " because " << error.message();
    ss.flush();
    ctx.raiseFatalError(msg);
  }
  llvm::StringRef pathAsStringRef(mutablePath.data(), mutablePath.size());
  toReturn.reset(
      new WorkingDirectoryManager(pathAsStringRef, ctx, deleteOnDestruction));
  return toReturn;
}

std::unique_ptr<WorkingDirectoryManager>
WorkingDirectoryManager::makeInDirectory(llvm::StringRef directory,
                                         llvm::StringRef prefix,
                                         jfs::core::JFSContext& ctx,
                                         bool deleteOnDestruction,
                                         uint16_t maxN) {
  assert(directory.size() > 0);
  assert(prefix.size() > 0);
  std::unique_ptr<WorkingDirectoryManager> toReturn(nullptr);
  llvm::SmallVector<char, 256> mutablePath(directory.begin(), directory.end());
  // Get `directory` as an absolute path.
  if (auto error = llvm::sys::fs::make_absolute(mutablePath)) {
    std::string msg;
    llvm::raw_string_ostream ss(msg);
    ss << "Failed to make " << directory << " absolute";
    ss.flush();
    ctx.raiseFatalError(msg);
  }
  // Check directory exists
  llvm::StringRef directoryAsStringRef(mutablePath.data(), mutablePath.size());
  if (!llvm::sys::fs::is_directory(directoryAsStringRef)) {
    std::string msg;
    llvm::raw_string_ostream ss(msg);
    ss << directoryAsStringRef << " is not an existing directory";
    ss.flush();
    ctx.raiseFatalError(msg);
    return toReturn;
  }
  // Add prefix
  llvm::sys::path::append(mutablePath, prefix);
  // Now loop through prefixes
  for (unsigned index = 0; index < maxN; ++index) {
    llvm::Twine tempNum(index);
    auto tempPath = llvm::Twine(mutablePath).concat("-");
    auto tempPathWithNum = tempPath.concat(tempNum);
    if (auto error =
            llvm::sys::fs::create_directory(tempPathWithNum,
                                            /*IgnoreExisting=*/false)) {
      if (error == std::errc::file_exists) {
        continue;
      }
      std::string msg;
      llvm::raw_string_ostream ss(msg);
      ss << "Failed to create " << tempPath << " because " << error.message();
      ss.flush();
      ctx.raiseFatalError(msg);
      return toReturn;
    }
    // Suceeded
    llvm::SmallVector<char, 256> tempBuffer;
    llvm::StringRef finalPathAsStringRef = tempPathWithNum.toStringRef(tempBuffer);
    toReturn.reset(new WorkingDirectoryManager(finalPathAsStringRef, ctx,
                                               deleteOnDestruction));
    return toReturn;
  }
  std::string msg;
  llvm::raw_string_ostream ss(msg);
  ss << "Failed to create directory in " << directory
     << " due to exhausting N (" << maxN << ")";
  ss.flush();
  ctx.raiseFatalError(msg);
  return toReturn;
}

std::string WorkingDirectoryManager::getPathToFileInDirectory(
    llvm::StringRef fileName) const {
  llvm::SmallVector<char, 256> mutablePath(path.begin(), path.end());
  llvm::sys::path::append(mutablePath, fileName);
  return llvm::Twine(mutablePath).str();
}

std::string
WorkingDirectoryManager::makeNewDirectoryInDirectory(llvm::StringRef dirName) {
  assert(dirName.size() > 0);
  std::string fullDirPath = getPathToFileInDirectory(dirName);
  if (auto error = llvm::sys::fs::create_directory(fullDirPath,
                                                   /*IgnoreExisting=*/false)) {
    std::string msg;
    llvm::raw_string_ostream ss(msg);
    ss << "Failed to create " << fullDirPath << " because " << error.message();
    ss.flush();
    ctx.raiseFatalError(msg);
  }
  return fullDirPath;
}
}
}
