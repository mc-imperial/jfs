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
#include "jfs/FuzzingCommon/CmdLine/SeedManagerOptionsBuilder.h"
#include "jfs/FuzzingCommon/CommandLineCategory.h"
#include "jfs/FuzzingCommon/SeedGenerator.h"
#include "jfs/FuzzingCommon/SeedManagerOptions.h"
#include "jfs/FuzzingCommon/SpecialConstantSeedGenerator.h"
#include "llvm/Support/CommandLine.h"

namespace {

llvm::cl::opt<unsigned> MaxSeedSpaceInBytes(
    "sm-max-seed-space",
    llvm::cl::desc("Maximum space total space for seeds in bytes. 0 means no "
                   "limit (default: 50 MiB)"),
    llvm::cl::init(50 * 1024 * 1024),
    llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<unsigned> MaxNumSeed(
    "sm-max-num-seed",
    llvm::cl::desc("Maximum number of seeds. 0 means no limit (default: 100)"),
    llvm::cl::init(100), llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<bool>
    AddAllZerosSeed("sm-all-zeros-seed",
                    llvm::cl::desc("Add seed of all zero bits (default: true)"),
                    llvm::cl::init(true),
                    llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<bool>
    AddAllOnesSeed("sm-all-ones-seed",
                   llvm::cl::desc("Add seed of all one bits (default: true)"),
                   llvm::cl::init(true),
                   llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));

llvm::cl::opt<bool> AddSpecialConstantSeeds(
    "sm-special-constant-seeds",
    llvm::cl::desc(
        "Add special constant seeds based on constraints (default: false)"),
    llvm::cl::init(false),
    llvm::cl::cat(jfs::fuzzingCommon::CommandLineCategory));
} // namespace

namespace jfs {
namespace fuzzingCommon {
namespace cl {

std::unique_ptr<jfs::fuzzingCommon::SeedManagerOptions>
buildSeedManagerOptionsFromCmdLine() {
  std::unique_ptr<SeedManagerOptions> opts(new SeedManagerOptions());
  opts->maxSeedSpaceInBytes = MaxSeedSpaceInBytes;
  opts->maxNumSeeds = MaxNumSeed;

  if (AddAllZerosSeed) {
    auto abeGen = std::unique_ptr<SeedGenerator>(
        new AllBytesEqualGenerator("zeros", /*byteValue=*/0));
    opts->generators.push_back(std::move(abeGen));
  }

  if (AddAllOnesSeed) {
    auto abeGen = std::unique_ptr<SeedGenerator>(
        new AllBytesEqualGenerator("ones", /*byteValue=*/0xff));
    opts->generators.push_back(std::move(abeGen));
  }

  if (AddSpecialConstantSeeds) {
    auto scsGen = std::unique_ptr<SeedGenerator>(
        new SpecialConstantSeedGenerator("special-constant"));
    opts->generators.push_back(std::move(scsGen));
  }

  return opts;
}
} // namespace cl
} // namespace fuzzingCommon
} // namespace jfs
