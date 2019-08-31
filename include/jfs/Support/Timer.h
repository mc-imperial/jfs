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
#ifndef JFS_SUPPORT_TIMER_H
#define JFS_SUPPORT_TIMER_H
#include "llvm/Support/Timer.h" // For llvm::TimeRecord

namespace jfs {
namespace support {

// This is timer inspired by `llvm::Timer`. Unfortunately `llvm::Timer` is a
// bit cumbersome to use due to the way it's tied to `TimerGroup`. We could
// potentially create `TimerGroup` for `StatisticsManager` and for each
// `JFSAggregateTimerStat` but we would need to keep all the `llvm::Timer`s
// alive so that the implicit dumping of stats to stderr happens properly.
// This seems wasteful so implementing our own seems simpler.
class Timer {
public:
  typedef llvm::TimeRecord RecordTy;

private:
  RecordTy Time;      ///< The total time captured.
  RecordTy StartTime; ///< The time startTimer() was last called.
  bool Running;       ///< Is the timer currently running?
  bool Triggered;     ///< Has the timer ever been triggered?
public:
  Timer();
  ~Timer();
  Timer(const Timer& RHS) = delete;

  /// Check if the timer is currently running.
  bool isRunning() const { return Running; }

  /// Check if startTimer() has ever been called on this timer.
  bool hasTriggered() const { return Triggered; }

  /// Start the timer running.  Time between calls to startTimer/stopTimer is
  /// counted by the Timer class.  Note that these calls must be correctly
  /// paired.
  void startTimer();

  /// Stop the timer.
  void stopTimer();

  /// Clear the timer state.
  void clear();

  /// Return the duration for which this timer has been running.
  RecordTy getTotalTime() const { return Time; }
};
}
}

#endif
