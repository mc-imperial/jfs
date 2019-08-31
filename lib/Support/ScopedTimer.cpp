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
#include "jfs/Support/ScopedTimer.h"
#include <chrono>
#include <condition_variable>
#include <thread>

namespace jfs {
namespace support {

class ScopedTimerImpl {
private:
  uint64_t maxTime;
  ScopedTimer::CallBackTy callBack;
  std::unique_ptr<std::thread> waiter;
  std::condition_variable cv;
  std::mutex cvMutex;
  bool realWakeUp;
  std::chrono::time_point<std::chrono::steady_clock> startTime;
  std::chrono::time_point<std::chrono::steady_clock> endTime;
  bool waiterStarted;

public:
  void waiterFunction() {
    std::unique_lock<std::mutex> lock(cvMutex);
    waiterStarted = true;
    // Loop just in case there are spurious wake ups
    while (true) {
      std::cv_status status = cv.wait_until(lock, endTime);
      if (status == std::cv_status::timeout) {
        callBack();
        break;
      }
      if (realWakeUp) {
        break;
      }
      // Spurious wake up. Just sleep again
    }
  }
  ScopedTimerImpl(uint64_t maxTime, ScopedTimer::CallBackTy callBack)
      : maxTime(maxTime), callBack(callBack), waiter(nullptr),
        realWakeUp(false), waiterStarted(false) {
    startTime = std::chrono::steady_clock::now();
    std::chrono::seconds timeout(maxTime);
    endTime = startTime + timeout;

    if (maxTime == 0) {
      return;
    }
    waiter.reset(new std::thread(&ScopedTimerImpl::waiterFunction, this));
  }
  ~ScopedTimerImpl() {
    if (waiter == nullptr)
      return;

    // Spin until `waiterFunction()` is waiting.  If we don't do this we might
    // call `notify_one()` before `waiterFunction()` is waiting and thus the
    // signal will be lost resulting in a deadlock when `waiter->join()` is
    // called.
    //
    // Given `waiterFunction()`'s implementation if `waiterStarted` is true
    // and we managed to grab the mutex then `waiter` thread must be waiting.
    while (true) {
      std::lock_guard<std::mutex> lock(cvMutex);
      if (waiterStarted) {
        // Wake up the thread if it's still running
        realWakeUp = true;
        break;
      }
    }
    cv.notify_one();
    if (waiter->joinable())
      waiter->join();
  }

  uint64_t getRemainingTime() const {
    auto now = std::chrono::steady_clock::now();
    auto remaining = endTime - now;
    auto remainingAsSecs =
        std::chrono::duration_cast<std::chrono::seconds>(remaining);
    int64_t remainingNativeTy = remainingAsSecs.count();
    if (remainingNativeTy < 0) {
      return 0;
    }
    return remainingNativeTy;
  }

  uint64_t getMaxTime() const { return maxTime; }
};

ScopedTimer::ScopedTimer(uint64_t maxTime, CallBackTy callBack)
    : impl(new ScopedTimerImpl(maxTime, callBack)) {}

ScopedTimer::~ScopedTimer() {
  // Let ~ScopedTimerImpl() do the work
}

uint64_t ScopedTimer::getRemainingTime() const {
  return impl->getRemainingTime();
}

uint64_t ScopedTimer::getMaxTime() const { return impl->getMaxTime(); }
}
}
