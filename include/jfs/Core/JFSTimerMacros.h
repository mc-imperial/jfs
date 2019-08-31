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
#ifndef JFS_CORE_JFS_TIMER_MACROS_H
#define JFS_CORE_JFS_TIMER_MACROS_H
#include "jfs/Core/JFSContext.h"
#include "jfs/Support/JFSStat.h"
#include "jfs/Support/ScopedJFSTimerStatAppender.h"
#include "jfs/Support/StatisticsManager.h"

#define JFS_SM_TIMER(NAME, CTX)                                                \
  jfs::support::ScopedJFSTimerStatAppender<jfs::support::StatisticsManager>    \
      NAME##_timer(((CTX).getConfig().gathericStatistics) ? (CTX.getStats())   \
                                                          : nullptr,           \
                   #NAME)

#define JFS_AG_TIMER(DECL_NAME, NAME, AG, CTX)                                 \
  jfs::support::ScopedJFSTimerStatAppender<                                    \
      jfs::support::JFSAggregateTimerStat>                                     \
      DECL_NAME##_timer(                                                       \
          ((CTX).getConfig().gathericStatistics) ? (AG.stats.get()) : nullptr, \
          (NAME))

#define JFS_AG_COL(NAME, CTX)                                                  \
  jfs::support::ScopedJFSAggregateTimerStatAppender<                           \
      jfs::support::StatisticsManager>                                         \
      NAME(((CTX).getConfig().gathericStatistics) ? (CTX.getStats())           \
                                                  : nullptr,                   \
           #NAME)
#endif
