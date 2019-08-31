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
#include "jfs/FuzzingCommon/JFSRuntimeFuzzingStat.h"
#include "jfs/Support/ErrorMessages.h"
#include "llvm/Support/MemoryBuffer.h"
#include "llvm/Support/YAMLTraits.h"

namespace llvm {
namespace yaml {

template <> struct MappingTraits<jfs::fuzzingCommon::JFSRuntimeFuzzingStat> {
  static void mapping(IO& io,
                      jfs::fuzzingCommon::JFSRuntimeFuzzingStat& stats) {
    io.mapOptional(jfs::fuzzingCommon::JFSRuntimeFuzzingStat::
                       maxNumConstraintsSatisfiedKeyName,
                   stats.maxNumConstraintsSatisfied);

    io.mapOptional(
        jfs::fuzzingCommon::JFSRuntimeFuzzingStat::numberOfInputsTriedKeyName,
        stats.numberOfInputsTried);

    io.mapOptional(jfs::fuzzingCommon::JFSRuntimeFuzzingStat::
                       numberOfWrongSizedInputsTriedKeyName,
                   stats.numberOfWrongSizedInputsTried);
  }
};
} // namespace yaml
} // namespace llvm

namespace jfs {
namespace fuzzingCommon {

const char* JFSRuntimeFuzzingStat::maxNumConstraintsSatisfiedKeyName =
    "jfs_max_num_const_sat";

const char* JFSRuntimeFuzzingStat::numberOfInputsTriedKeyName =
    "jfs_num_inputs";

const char* JFSRuntimeFuzzingStat::numberOfWrongSizedInputsTriedKeyName =
    "jfs_num_wrong_size_inputs";

// FIXME: We need sentinel values for these stats so we know if they
// weren't set vs their value actually is 0.
JFSRuntimeFuzzingStat::JFSRuntimeFuzzingStat(llvm::StringRef name)
    : JFSStat(RUNTIME, name), maxNumConstraintsSatisfied(0),
      numberOfInputsTried(0), numberOfWrongSizedInputsTried(0) {}

JFSRuntimeFuzzingStat::~JFSRuntimeFuzzingStat() {}

void JFSRuntimeFuzzingStat::printYAML(llvm::ScopedPrinter& sp) const {
  sp.indent();
  auto& os = sp.getOStream();
  // NOTE: Can't use `llvm::yaml::Output` here due to
  //
  // * Document delimiters it adds.
  // * A mismtach between what we parse and load (the `name` field).
  // * Indentation not being respected
  os << "\n";
  sp.startLine() << "name: " << getName() << "\n";
  sp.startLine() << maxNumConstraintsSatisfiedKeyName << ": "
                 << maxNumConstraintsSatisfied << "\n";
  sp.startLine() << numberOfInputsTriedKeyName << ": " << numberOfInputsTried
                 << "\n";
  sp.startLine() << numberOfWrongSizedInputsTriedKeyName << ": "
                 << numberOfWrongSizedInputsTried << "\n";
  sp.unindent();
}

std::unique_ptr<JFSRuntimeFuzzingStat>
JFSRuntimeFuzzingStat::LoadFromYAML(llvm::StringRef filePath,
                                    llvm::StringRef name,
                                    jfs::core::JFSContext& ctx) {
  auto bufferOrError = llvm::MemoryBuffer::getFile(filePath);
  if (auto error = bufferOrError.getError()) {
    ctx.getErrorStream() << jfs::support::getMessageForFailedOpenFileOrSTDIN(
        filePath, error);
    return nullptr;
  }
  auto buffer(std::move(bufferOrError.get()));
  auto mbr = buffer->getMemBufferRef();
  llvm::yaml::Input yin(mbr);
  std::unique_ptr<JFSRuntimeFuzzingStat> stats(new JFSRuntimeFuzzingStat(name));
  yin >> *stats;
  if (auto error = yin.error()) {
    ctx.getErrorStream() << "(error parsing failure \"" << error.message()
                         << "\")\n";
    return nullptr;
  }
  return stats;
}

} // namespace fuzzingCommon
} // namespace jfs
