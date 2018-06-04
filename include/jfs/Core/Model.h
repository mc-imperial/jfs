//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017-2018 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#ifndef JFS_CORE_MODEL_H
#define JFS_CORE_MODEL_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Z3Node.h"
#include <string>

namespace jfs {
namespace core {

class Model {
protected:
  jfs::core::Z3ModelHandle z3Model;
  JFSContext& ctx;
  Model(JFSContext& ctx);

public:
  virtual Z3ASTHandle getAssignmentFor(Z3FuncDeclHandle);
  virtual bool addAssignmentFor(Z3FuncDeclHandle decl, Z3ASTHandle e,
                                bool allowOverwrite = false);
  virtual std::string getSMTLIBString();
  virtual bool hasAssignmentFor(Z3FuncDeclHandle decl);
  virtual Z3ModelHandle getRepr() { return z3Model; }
  JFSContext& getContext();
  virtual ~Model();
};

} // namespace core
} // namespace jfs
#endif
