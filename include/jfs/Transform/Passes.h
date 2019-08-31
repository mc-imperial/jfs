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
#include "jfs/Transform/AndHoistingPass.h"
#include "jfs/Transform/BitBlastPass.h"
#include "jfs/Transform/BvBoundPropagationPass.h"
#include "jfs/Transform/ConstantPropagationPass.h"
#include "jfs/Transform/DIMACSOutputPass.h"
#include "jfs/Transform/DuplicateConstraintEliminationPass.h"
#include "jfs/Transform/FpToBvPass.h"
#include "jfs/Transform/SimpleContradictionsToFalsePass.h"
#include "jfs/Transform/SimplificationPass.h"
#include "jfs/Transform/TrueConstraintEliminationPass.h"
