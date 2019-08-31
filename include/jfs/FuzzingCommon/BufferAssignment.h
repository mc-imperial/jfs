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
#ifndef JFS_FUZZING_COMMON_BUFFER_ASSIGNMENT
#define JFS_FUZZING_COMMON_BUFFER_ASSIGNMENT
#include "jfs/Core/Query.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeMap.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/FuzzingCommon/BufferElement.h"
#include <vector>

namespace jfs {
namespace fuzzingCommon {

class BufferAssignment {
private:
  typedef std::vector<BufferElement> ChunksTy;
  ChunksTy chunks;
  uint64_t cachedTypeBitWidth;
  uint64_t cachedStoreBitWidth;
  uint64_t computeTypeBitWidth() const;
  uint64_t computeStoreBitWidth() const;

public:
  BufferAssignment() : cachedTypeBitWidth(0), cachedStoreBitWidth(0) {}
  ~BufferAssignment() {}
  void appendElement(BufferElement&);
  uint64_t getTypeBitWidth() const { return cachedTypeBitWidth; }
  uint64_t getStoreBitWidth() const { return cachedStoreBitWidth; }
  uint64_t getRequiredStoreBytes() const {
    return (getStoreBitWidth() + 7) / 8;
  }
  ChunksTy::const_iterator cbegin() const { return chunks.begin(); }
  ChunksTy::const_iterator cend() const { return chunks.end(); }
  ChunksTy::const_iterator begin() const { return cbegin(); }
  ChunksTy::const_iterator end() const { return cend(); }
  size_t size() const { return chunks.size(); }
  void print(llvm::raw_ostream&) const;
  void dump() const;
};

} // namespace fuzzingCommon
} // namespace jfs
#endif
