//===----------------------------------------------------------------------===//
//
//                        JFS - The JIT Fuzzing Solver
//
// Copyright 2017 Daniel Liew
//
// This file is distributed under the MIT license.
// See LICENSE.txt for details.
//
//===----------------------------------------------------------------------===//
#include "jfs/Support/JFSStat.h"

namespace jfs {
namespace support {

// JFSStat
JFSStat::JFSStat(JFSStatKind kind, llvm::StringRef name) : kind(kind) {
  this->name.assign(name.begin(), name.end());
}
void JFSStat::dump() const {
  llvm::ScopedPrinter sp(llvm::errs());
  printYAML(sp);
}

llvm::StringRef JFSStat::getName() const { return name; }

// JFSTimerStat
JFSTimerStat::JFSTimerStat(RecordTy record, llvm::StringRef name)
    : JFSStat(SINGLE_TIMER, name), record(record) {}
JFSTimerStat::~JFSTimerStat() {}
void JFSTimerStat::printYAML(llvm::ScopedPrinter& os) const {
  // TODO
}

// JFSAggregateTimerStat
JFSAggregateTimerStat::JFSAggregateTimerStat(llvm::StringRef name)
    : JFSStat(AGGREGATE_TIMER, name) {}

JFSAggregateTimerStat::~JFSAggregateTimerStat() {}

void JFSAggregateTimerStat::append(std::unique_ptr<JFSTimerStat> t) {
  timers.push_back(std::move(t));
}

void JFSAggregateTimerStat::clear() { timers.clear(); }

void JFSAggregateTimerStat::printYAML(llvm::ScopedPrinter& os) const {
  // TODO
}
}
}
