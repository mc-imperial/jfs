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
#ifndef JFS_CORE_MODEL_H
#define JFS_CORE_MODEL_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Core/Z3Node.h"
#include <string>

namespace jfs {
namespace core {

struct ModelPrintOptions {
  bool sortDecls = false;
  bool useModelKeyword = false;
};

class Model {
protected:
  jfs::core::Z3ModelHandle z3Model;
  JFSContext& ctx;
  Model(JFSContext& ctx);

public:
  // The idea behind this interface is to allow implementations
  // to defer working with Z3ModelHandle and only forcing use when
  // `getRepr()` is called. At the time of writing no implementations
  // actually do this so perhaps we should remove this complexity?
  virtual Z3ASTHandle getAssignmentFor(Z3FuncDeclHandle);
  virtual bool addAssignmentFor(Z3FuncDeclHandle decl, Z3ASTHandle e,
                                bool allowOverwrite = false);
  virtual std::string getSMTLIBString(ModelPrintOptions* opts = nullptr);
  virtual bool hasAssignmentFor(Z3FuncDeclHandle decl);
  virtual Z3ModelHandle getRepr() { return z3Model; }
  virtual bool replaceRepr(Z3ModelHandle replacement);
  virtual Z3ASTHandle evaluate(Z3ASTHandle e, bool modelCompletion);

  JFSContext& getContext();
  virtual ~Model();

  static Z3ASTHandle getDefaultValueFor(Z3SortHandle sort);
};

} // namespace core
} // namespace jfs
#endif
