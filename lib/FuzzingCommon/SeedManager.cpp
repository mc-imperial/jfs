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
#include "jfs/FuzzingCommon/SeedManager.h"
#include "jfs/Core/IfVerbose.h"
#include "jfs/Core/JFSTimerMacros.h"
#include "jfs/FuzzingCommon/FuzzingAnalysisInfo.h"
#include "jfs/FuzzingCommon/SeedGenerator.h"
#include "jfs/FuzzingCommon/SeedManagerOptions.h"
#include "jfs/FuzzingCommon/SeedManagerStat.h"
#include "llvm/Support/Path.h"
#include <list>
#include <unordered_map>

namespace jfs {
namespace fuzzingCommon {

using namespace jfs::core;

class SeedManagerImpl {
public:
  using GeneratorContainerTy = std::list<std::unique_ptr<SeedGenerator>>;
  bool cancelled = false;
  SeedManager* wrapper;
  GeneratorContainerTy activeGenerators;
  GeneratorContainerTy emptyGenerators;
  std::string seedDir;
  JFSContext& ctx;
  // Right now we don't actually store the seedIDs. We could do
  // in the future if for some reason we need to iterate over them
  // but the current algorithm means we can actually infer the used
  // seed IDs from `prefixToCounterMap`.
  std::unordered_map<std::string, uint64_t> prefixToCounterMap;
  uint64_t numRequestedIDs = 0;
  uint64_t maxSeedSpaceInBytes = 0;
  uint64_t maxNumSeeds = 0;
  uint64_t seedSize = 0;
  const FuzzingAnalysisInfo* fai;
  const Query* query;
  llvm::SmallVector<char, 256> mutablePath;
  SeedManagerImpl(SeedManager* wrapper, llvm::StringRef seedDir,
                  jfs::core::JFSContext& ctx)
      : wrapper(wrapper), seedDir(seedDir), ctx(ctx), fai(nullptr),
        query(nullptr) {
    assert(llvm::sys::path::is_absolute(llvm::Twine(seedDir)));
    mutablePath.insert(mutablePath.begin(), seedDir.begin(), seedDir.end());
  }

  ~SeedManagerImpl() {}

  void cancel() { cancelled = true; }

  void configureFrom(std::unique_ptr<SeedManagerOptions> options) {
    setSpaceLimit(options->maxSeedSpaceInBytes);
    setMaxNumSeeds(options->maxNumSeeds);
    if (activeGenerators.size() == 0) {
      activeGenerators = std::move(options->generators);
    } else {
      for (auto& genPtr : options->generators) {
        activeGenerators.push_back(std::move(genPtr));
      }
    }
  }

  void addSeedGenerator(std::unique_ptr<SeedGenerator> sg) {
    assert(sg && "SeedGenerator cannot be null");
    activeGenerators.push_back(std::move(sg));
  }

  uint64_t writeSeeds(const FuzzingAnalysisInfo* info,
                      const jfs::core::Query* q) {
    uint64_t numSeedsWritten = 0;
    auto bufferAssignment = info->freeVariableAssignment->bufferAssignment;
    this->seedSize = bufferAssignment->getRequiredStoreBytes();
    this->fai = info;
    this->query = q;
    if (seedSize == 0) {
      // The buffer is empty so we don't generate any seeds.
      return numSeedsWritten;
    }
    uint64_t boundBasedOnSpace = getSpaceLimit() / seedSize;
    uint64_t effectiveBound =
        std::min(((getSpaceLimit() > 0) ? boundBasedOnSpace : UINT64_MAX),
                 ((getMaxNumSeeds() > 0) ? getMaxNumSeeds() : UINT64_MAX));

    IF_VERB(ctx, ctx.getDebugStream() << "(SeedManager effectiveBound:"
                                      << effectiveBound << ")\n");

#define CHECK_CANCELLED()                                                      \
  if (cancelled) {                                                             \
    IF_VERB(ctx, ctx.getDebugStream() << "(SeedManager cancelled)\n");         \
    return numSeedsWritten;                                                    \
  }
    {
      JFS_SM_TIMER(add_fuzzer_seeds, ctx);
      // Do call back on all generators
      for (auto& g : activeGenerators) {
        CHECK_CANCELLED();
        g->preGenerationCallBack(*wrapper);
      }

      // Go through the seed generators round robin until we hit a bound or
      // we've exhausted the seed generators
      GeneratorContainerTy::iterator gen = activeGenerators.begin();
      while (numSeedsWritten < effectiveBound) {
        CHECK_CANCELLED();
        if (activeGenerators.size() == 0) {
          IF_VERB(ctx, ctx.getDebugStream()
                           << "(SeedManager active generators exhausted)\n");
          break;
        }
        if (gen == activeGenerators.end()) {
          // Hit the end of list of generators. Start again from the beginning.
          gen = activeGenerators.begin();
          continue;
        }
        if ((*gen)->empty()) {
          // This seed generator is empty. Remove it from list of active
          // generators.
          emptyGenerators.push_back(std::move(*gen));
          gen = activeGenerators.erase(gen);
          continue;
        }
        // Generate seed
        assert(!((*gen)->empty()) && "SeedGenerator cannot be empty");
        bool success = (*gen)->writeSeed(*wrapper);
        if (!success) {
          ctx.raiseFatalError("Failed to write seed");
        } else {
          ++numSeedsWritten;
        }
      }
      // Do post seed generation call backs
      for (auto& g : activeGenerators) {
        CHECK_CANCELLED();
        g->postGenerationCallBack(*wrapper);
      }
      for (auto& g : emptyGenerators) {
        CHECK_CANCELLED();
        g->postGenerationCallBack(*wrapper);
      }
    }

    IF_VERB(ctx, ctx.getDebugStream()
                     << "(SeedManager wrote " << numSeedsWritten << " seeds ("
                     << seedSize << " bytes each))\n");
    // Add Stats
    if (ctx.getStats() != nullptr) {
      std::unique_ptr<SeedManagerStat> smStats(
          new SeedManagerStat("SeedManager"));
      smStats->numSeedsGenerated = numSeedsWritten;
      ctx.getStats()->append(std::move(smStats));
    }
    return numSeedsWritten;
  }

  void setSpaceLimit(uint64_t maxSeedSpaceInBytes) {
    this->maxSeedSpaceInBytes = maxSeedSpaceInBytes;
  }
  uint64_t getSpaceLimit() const { return maxSeedSpaceInBytes; }
  void setMaxNumSeeds(uint64_t maxNumSeeds) { this->maxNumSeeds = maxNumSeeds; }
  uint64_t getMaxNumSeeds() const { return maxNumSeeds; }

  std::unique_ptr<llvm::FileOutputBuffer>
  getBufferForSeed(llvm::StringRef prefix) {
    assert(seedSize > 0);
    std::string seedID = getAndReserveSeedID(prefix);
    llvm::sys::path::append(mutablePath, seedID);
    // Apparently it's okay for a null terminator to not be included in the size
    llvm::StringRef fullPathToSeed(mutablePath.data(), mutablePath.size());
    IF_VERB(ctx, ctx.getDebugStream() << "(SeedManager creating seed \""
                                      << fullPathToSeed << "\")\n");
    auto expectFob = llvm::FileOutputBuffer::create(fullPathToSeed, seedSize);
    std::unique_ptr<llvm::FileOutputBuffer> fob = nullptr;
    if (expectFob) {
      fob = std::move(*expectFob);
    } else {
      // Failed
      ctx.getErrorStream()
          << "(error Failed to created FileOutputBuffer for seed)\n";
    }

    // Reset for next call
    llvm::sys::path::remove_filename(mutablePath);
    return fob;
  }

  std::string getAndReserveSeedID(llvm::StringRef prefix) {
    ++numRequestedIDs;
    std::string key(prefix);
    std::string underlyingString;
    llvm::raw_string_ostream ss(underlyingString);
    ss << prefix << "_";
    uint64_t suffixInt = 0;
    auto it = prefixToCounterMap.find(key);
    if (it == prefixToCounterMap.end()) {
      prefixToCounterMap[key] = 0;
    } else {
      suffixInt = ++(it->second);
    }
    ss << suffixInt;
    return ss.str();
    ;
  }

  jfs::core::JFSContext& getContext() const { return ctx; }

  const FuzzingAnalysisInfo* getCurrentFuzzingAnalysisInfo() const {
    return fai;
  }

  const jfs::core::Query* getCurrentQuery() const { return query; }
};

SeedManager::SeedManager(llvm::StringRef seedDir, JFSContext& ctx)
    : impl(new SeedManagerImpl(this, seedDir, ctx)) {}

SeedManager::~SeedManager() {}

void SeedManager::configureFrom(std::unique_ptr<SeedManagerOptions> options) {
  impl->configureFrom(std::move(options));
}

void SeedManager::addSeedGenerator(std::unique_ptr<SeedGenerator> sg) {
  impl->addSeedGenerator(std::move(sg));
}
// Returns number of written seeds.
uint64_t SeedManager::writeSeeds(const FuzzingAnalysisInfo* info,
                                 const jfs::core::Query* q) {
  return impl->writeSeeds(info, q);
}

void SeedManager::setSpaceLimit(uint64_t maxTotalInBytes) {
  impl->setSpaceLimit(maxTotalInBytes);
}

uint64_t SeedManager::getSpaceLimit() const { return impl->getSpaceLimit(); }

void SeedManager::setMaxNumSeeds(uint64_t maxNumSeeds) {
  impl->setMaxNumSeeds(maxNumSeeds);
}
uint64_t SeedManager::getMaxNumSeeds() const { return impl->getMaxNumSeeds(); }

std::unique_ptr<llvm::FileOutputBuffer>
SeedManager::getBufferForSeed(llvm::StringRef prefix) {
  return impl->getBufferForSeed(prefix);
}

std::string SeedManager::getAndReserveSeedID(llvm::StringRef prefix) {
  return impl->getAndReserveSeedID(prefix);
}

std::string SeedManager::getAndReserveSeedID() {
  return impl->getAndReserveSeedID("");
}

jfs::core::JFSContext& SeedManager::getContext() const {
  return impl->getContext();
}

const FuzzingAnalysisInfo* SeedManager::getCurrentFuzzingAnalysisInfo() const {
  return impl->getCurrentFuzzingAnalysisInfo();
}
const jfs::core::Query* SeedManager::getCurrentQuery() const {
  return impl->getCurrentQuery();
}

void SeedManager::cancel() { impl->cancel(); }

} // namespace fuzzingCommon
} // namespace jfs
