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
#include "jfs/Support/Timer.h"

using namespace llvm;

namespace jfs {
namespace support {

Timer::Timer() : Running(false), Triggered(false) {}
Timer::~Timer() {}

void Timer::startTimer() {
  assert(!Running && "Cannot start a running timer");
  Running = Triggered = true;
  StartTime = TimeRecord::getCurrentTime(true);
}

void Timer::stopTimer() {
  assert(Running && "Cannot stop a paused timer");
  Running = false;
  Time += TimeRecord::getCurrentTime(false);
  Time -= StartTime;
}

void Timer::clear() {
  Running = Triggered = false;
  Time = StartTime = TimeRecord();
}
}
}
