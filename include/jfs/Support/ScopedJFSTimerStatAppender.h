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
#ifndef JFS_SUPPORT_SCOPED_JFS_TIMER_STAT_APPENDER_H
#define JFS_SUPPORT_SCOPED_JFS_TIMER_STAT_APPENDER_H
#include "jfs/Support/JFSStat.h"
#include "jfs/Support/Timer.h"
#include <memory>

namespace jfs {
namespace support {

template <typename T> class ScopedJFSTimerStatAppender {
public:
  T* receiver;
  Timer timer;
  llvm::StringRef name;
  std::unique_ptr<JFSTimerStat> result;
  ScopedJFSTimerStatAppender(T* receiver, llvm::StringRef name)
      : receiver(receiver), timer(), name(name), result(nullptr) {
    if (receiver == nullptr)
      return;
    // Start timer
    timer.startTimer();
  }
  ~ScopedJFSTimerStatAppender() {
    if (receiver == nullptr)
      return;
    timer.stopTimer();
    result.reset(new JFSTimerStat(timer.getTotalTime(), name));
    receiver->append(std::move(result));
  }
};

template <typename T> class ScopedJFSAggregateTimerStatAppender {
public:
  T* receiver;
  std::unique_ptr<JFSAggregateTimerStat> stats;
  ScopedJFSAggregateTimerStatAppender(T* receiver, llvm::StringRef name)
      : receiver(receiver), stats(nullptr) {
    if (receiver == nullptr)
      return;
    stats.reset(new JFSAggregateTimerStat(name));
  }
  ~ScopedJFSAggregateTimerStatAppender() {
    if (receiver == nullptr)
      return;
    receiver->append(std::move(stats));
  }
};
}
}

#endif
