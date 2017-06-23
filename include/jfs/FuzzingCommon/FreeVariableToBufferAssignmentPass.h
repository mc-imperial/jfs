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
#ifndef JFS_FUZZING_COMMON_FREE_VARIABLE_TO_BUFFER_ASSIGNMENT_PASS_H
#define JFS_FUZZING_COMMON_FREE_VARIABLE_TO_BUFFER_ASSIGNMENT_PASS_H
#include "jfs/Core/Query.h"
#include "jfs/Core/Z3Node.h"
#include "jfs/Core/Z3NodeMap.h"
#include "jfs/Core/Z3NodeSet.h"
#include "jfs/FuzzingCommon/EqualityExtractionPass.h"
#include "jfs/Transform/QueryPass.h"
#include <vector>

namespace jfs {
namespace fuzzingCommon {

class BufferElement {
public:
  const jfs::core::Z3ASTHandle declApp;
  BufferElement(const jfs::core::Z3ASTHandle declApp);
  unsigned getBitWidth() const;
  // FIXME: put this behind an interface once we know the requirements
  std::vector<jfs::core::Z3ASTHandle> equalities;
  void print(llvm::raw_ostream&) const;
  void dump() const;
  jfs::core::Z3FuncDeclHandle getDecl() const;
  std::string getName() const;
  jfs::core::Z3SortHandle getSort() const;
};

class BufferAssignment {
private:
  typedef std::vector<BufferElement> ChunksTy;
  ChunksTy chunks;

public:
  BufferAssignment() {}
  ~BufferAssignment() {}
  void appendElement(BufferElement&);
  unsigned computeWidth() const;
  ChunksTy::const_iterator cbegin() const { return chunks.begin(); }
  ChunksTy::const_iterator cend() const { return chunks.end(); }
  ChunksTy::const_iterator begin() const { return cbegin(); }
  ChunksTy::const_iterator end() const { return cend(); }
  size_t size() const { return chunks.size(); }
  void print(llvm::raw_ostream&) const;
  void dump() const;
};

class ConstantAssignment {
public:
  // TODO: Put this behind an interface
  jfs::core::Z3ASTMap<jfs::core::Z3ASTHandle> assignments;
  void print(llvm::raw_ostream&) const;
  void dump() const;
};

class FreeVariableToBufferAssignmentPass : public jfs::transform::QueryPass {
private:
  const EqualityExtractionPass& eep;

public:
  FreeVariableToBufferAssignmentPass(const EqualityExtractionPass&);
  ~FreeVariableToBufferAssignmentPass() {}
  bool run(jfs::core::Query& q) override;
  virtual llvm::StringRef getName() override;
  // TODO: Put these behind an interface
  std::shared_ptr<BufferAssignment> bufferAssignment;
  // FIXME: It's debatable whether we actually need this. The
  // ConstantPropagation pass
  // means that equalities like this will already be expanded in constraints.
  // This means
  // the free variables that have constant assignments will never be used once
  // the
  // EqualityExtractionPass has run and so constantAssignment is always empty.
  std::shared_ptr<ConstantAssignment> constantAssignments;
};
}
}

#endif
