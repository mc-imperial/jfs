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
#ifndef JFS_FUZZING_COMMON_SEED_MANAGER_H
#define JFS_FUZZING_COMMON_SEED_MANAGER_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Query.h"
#include "jfs/Support/ICancellable.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/FileOutputBuffer.h"
#include <list>
#include <memory>

namespace jfs {
namespace fuzzingCommon {

class SeedGenerator;
class SeedManagerImpl;
class FuzzingAnalysisInfo;
class SeedManagerOptions;

class SeedManager : jfs::support::ICancellable {
private:
  std::unique_ptr<SeedManagerImpl> impl;

public:
  SeedManager(llvm::StringRef seedDir, jfs::core::JFSContext& ctx);
  SeedManager(const SeedManager&) = delete;
  ~SeedManager();
  void cancel() override;
  void configureFrom(std::unique_ptr<SeedManagerOptions> options);
  void addSeedGenerator(std::unique_ptr<SeedGenerator> sg);
  // Returns number of written seeds.
  uint64_t writeSeeds(const FuzzingAnalysisInfo* info,
                      const jfs::core::Query* q);

  void setSpaceLimit(uint64_t maxSeedSpaceInBytes);
  uint64_t getSpaceLimit() const;
  void setMaxNumSeeds(uint64_t maxNumSeeds);
  uint64_t getMaxNumSeeds() const;

  // Create a FileOutputBuffer with the appropriate size and filename for the
  // seed. The caller is responsible for calling commit.
  //
  // This is the preferred method writing a seed
  std::unique_ptr<llvm::FileOutputBuffer>
  getBufferForSeed(llvm::StringRef prefix);

  // Get and reserve a seed ID but don't actually create it.
  std::string getAndReserveSeedID(llvm::StringRef prefix);
  std::string getAndReserveSeedID();

  jfs::core::JFSContext& getContext() const;
  const FuzzingAnalysisInfo* getCurrentFuzzingAnalysisInfo() const;
  const jfs::core::Query* getCurrentQuery() const;
};

} // namespace fuzzingCommon
} // namespace jfs

#endif
