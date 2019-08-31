//===----------------------------------------------------------------------===//
//
//                                     JFS
//
// Copyright 2017-2018 Alastair Donaldson
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_FUZZING_COMMON_FILE_SERIALIZABLE_MODEL_H
#define JFS_FUZZING_COMMON_FILE_SERIALIZABLE_MODEL_H
#include "jfs/Core/Model.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/FuzzingCommon/BufferAssignment.h"
#include "llvm/Support/FileOutputBuffer.h"
#include "llvm/Support/MemoryBuffer.h"
#include <memory>

namespace jfs {
namespace fuzzingCommon {

class FileSerializableModel : public jfs::core::Model {
public:
  // Empty model
  FileSerializableModel(jfs::core::JFSContext& ctx);

  static std::unique_ptr<FileSerializableModel>
  loadFrom(const llvm::MemoryBuffer* buf, const BufferAssignment* ba,
           jfs::core::JFSContext& ctx);

  bool saveTo(llvm::FileOutputBuffer* buf, const BufferAssignment* ba,
              jfs::core::JFSContext& ctx);
};

} // namespace fuzzingCommon
} // namespace jfs
#endif
