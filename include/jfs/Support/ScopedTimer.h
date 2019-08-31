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
#ifndef JFS_SUPPORT_SCOPED_TIMER_H
#define JFS_SUPPORT_SCOPED_TIMER_H
#include <functional>
#include <memory>
#include <stdint.h>

namespace jfs {
namespace support {

class ScopedTimerImpl;

class ScopedTimer {
private:
  std::unique_ptr<ScopedTimerImpl> impl;

public:
  typedef std::function<void(void)> CallBackTy;
  // Will call `callBack` if wall clock time exceeds
  // `maxTime`. If `maxTime` is == 0 then `callBack`
  // will never be called.
  ScopedTimer(uint64_t maxTime, CallBackTy callBack);
  ~ScopedTimer();
  uint64_t getRemainingTime() const;
  uint64_t getMaxTime() const;
};
}
}

#endif
