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
#include "jfs/Transform/Z3QueryPass.h"

using namespace jfs::core;

namespace jfs {
namespace transform {

void Z3QueryPass::cancel() {
  cancelled = true;
  // Interupt Z3 just in case we are in the middle
  // of an application.
  // FIXME: This is racey
  if (z3Ctx) {
    ::Z3_interrupt(z3Ctx);
  }
}

bool Z3QueryPass::convertModel(jfs::core::Model* m) {
  // FIXME: We should prevent interruption with a lock.

  // We assume that the sub class stored the Z3ApplyResultHandle
  // from applying a tactic in `result`.
  assert(!result.isNull());

  // Is this the right approach? Z3's API applies model conversion for
  // model intended for each sub-goal. We don't solve that way though so
  // we have only one model. Just try to iteratively apply model conversion
  // of the same model for each sub-goal.
  Z3ModelHandle mh = m->getRepr();
  for (unsigned goalIndex = 0; goalIndex < result.getNumGoals(); ++goalIndex) {
    assert(!mh.isNull());
    mh = result.convertModelForGoal(goalIndex, mh);
  }
  assert(!mh.isNull());
  // AFAICT Z3's implementation copies the provided model rather than modifying
  // in-place. This means we have to modify the `jfs::core::Model` to use the
  // copy.
  bool success = m->replaceRepr(mh);
  if (!success) {
    m->getContext().raiseFatalError("Failed to replace model representation");
  }
  return success;
}
}
}
