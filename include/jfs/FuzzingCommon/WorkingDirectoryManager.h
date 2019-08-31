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
#ifndef JFS_FUZZING_COMMON_WORKING_DIRECTORY_MANAGER_H
#define JFS_FUZZING_COMMON_WORKING_DIRECTORY_MANAGER_H
#include "jfs/Core/JFSContext.h"
#include "llvm/ADT/StringRef.h"
#include <memory>
#include <string>

namespace jfs {
namespace fuzzingCommon {

class WorkingDirectoryManager {
private:
  const std::string path;
  jfs::core::JFSContext& ctx;
  const bool deleteOnDestruction;
  WorkingDirectoryManager(llvm::StringRef path, jfs::core::JFSContext& ctx,
                          bool deleteOnDestruction);

public:
  // Don't allow copying
  ~WorkingDirectoryManager();
  WorkingDirectoryManager(const WorkingDirectoryManager&) = delete;
  WorkingDirectoryManager(const WorkingDirectoryManager&&) = delete;
  WorkingDirectoryManager& operator=(const WorkingDirectoryManager&) = delete;

  llvm::StringRef getPath() const { return path; }
  std::string getPathToFileInDirectory(llvm::StringRef fileName) const;
  std::string makeNewDirectoryInDirectory(llvm::StringRef dirName);

  // Make at `path`. `path` should not already exist, but its
  // parent directory should.
  // If the fails a nullptr will be returned.
  static std::unique_ptr<WorkingDirectoryManager>
  makeAtPath(llvm::StringRef path, jfs::core::JFSContext& ctx,
             bool deleteOnDestruction);

  // Make at `<directory>/<prefix>-N` where `N` is an integer.
  // This function will start with `N == 0` an keep incrementing
  // `N` until a directory is successfully created `N == maxN`.
  // If the fails a nullptr will be returned.
  static std::unique_ptr<WorkingDirectoryManager>
  makeInDirectory(llvm::StringRef directory, llvm::StringRef prefix,
                  jfs::core::JFSContext& ctx, bool deleteOnDestruction,
                  uint16_t maxN = 100);
};
}
}

#endif
