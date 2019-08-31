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
#include "jfs/Support/JFSStat.h"
#include "llvm/Support/Format.h"

namespace jfs {
namespace support {

// JFSStat
JFSStat::JFSStat(JFSStatKind kind, llvm::StringRef name) : kind(kind) {
  this->name.assign(name.begin(), name.end());
}

JFSStat::~JFSStat() {}

void JFSStat::dump() const {
  llvm::ScopedPrinter sp(llvm::errs());
  printYAML(sp);
}

llvm::StringRef JFSStat::getName() const { return name; }

// JFSTimerStat
JFSTimerStat::JFSTimerStat(RecordTy record, llvm::StringRef name)
    : JFSStat(SINGLE_TIMER, name), record(record) {}
JFSTimerStat::~JFSTimerStat() {}

void JFSTimerStat::printYAML(llvm::ScopedPrinter& sp) const {
  sp.indent();
  auto& os = sp.getOStream();
  os << "\n";
  sp.startLine() << "name: " << getName() << "\n";
#define TIME_FMT_STR "%.6f"
  sp.startLine() << "user_time: "
                 << llvm::format(TIME_FMT_STR, record.getUserTime()) << "\n";
  sp.startLine() << "sys_time: "
                 << llvm::format(TIME_FMT_STR, record.getSystemTime()) << "\n";
  sp.startLine() << "wall_time: "
                 << llvm::format(TIME_FMT_STR, record.getWallTime()) << "\n";
  sp.startLine() << "mem_use: " << record.getMemUsed() << "\n";
#undef TIME_FMT_STR
  sp.unindent();
}

// JFSAggregateTimerStat
JFSAggregateTimerStat::JFSAggregateTimerStat(llvm::StringRef name)
    : JFSStat(AGGREGATE_TIMER, name) {}

JFSAggregateTimerStat::~JFSAggregateTimerStat() {}

void JFSAggregateTimerStat::append(std::unique_ptr<JFSTimerStat> t) {
  timers.push_back(std::move(t));
}

void JFSAggregateTimerStat::clear() { timers.clear(); }

void JFSAggregateTimerStat::printYAML(llvm::ScopedPrinter& sp) const {
  sp.indent();
  auto& os = sp.getOStream();
  os << "\n";
  sp.startLine() << "name: " << getName() << "\n";
  sp.startLine() << "stats:";
  if (timers.size() == 0) {
    os << " []\n";
    return;
  }
  os << "\n";
  sp.indent();
  for (const auto& stat : timers) {
    sp.startLine() << "-";
    stat->printYAML(sp);
  }
  sp.unindent();
  sp.unindent();
}
}
}
