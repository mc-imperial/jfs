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
#include "jfs/Core/SimpleModel.h"

namespace jfs {
namespace core {

SimpleModel::SimpleModel(JFSContext& ctx) : Model(ctx) {
  z3Model = Z3ModelHandle(::Z3_mk_model(ctx.getZ3Ctx()), ctx.getZ3Ctx());
}
} // namespace core
} // namespace jfs
