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
#ifndef JFS_SUPPORT_JFS_STAT_H
#define JFS_SUPPORT_JFS_STAT_H
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/ScopedPrinter.h"
#include "llvm/Support/Timer.h"
#include "llvm/Support/raw_ostream.h"
#include <list>
#include <memory>
#include <string>

namespace jfs {
namespace support {

class JFSStat {
public:
  enum JFSStatKind {
    SINGLE_TIMER,
    AGGREGATE_TIMER,
    CXX_PROGRAM,
    RUNTIME,
    SEED_MANAGER,
    SEED_GENERATOR
  };

private:
  const JFSStatKind kind;
  std::string name;

protected:
  JFSStat(JFSStatKind kind, llvm::StringRef name);

public:
  virtual ~JFSStat();
  JFSStatKind getKind() const { return kind; }
  // FIXME: We should switch to llvm::yaml API.
  virtual void printYAML(llvm::ScopedPrinter& os) const = 0;
  void dump() const;
  llvm::StringRef getName() const;
};

class JFSAggregateTimerStat;
class JFSTimerStat : public JFSStat {
private:
  using RecordTy = llvm::TimeRecord;
  RecordTy record;

public:
  friend class JFSAggregateTimerStat;
  JFSTimerStat(RecordTy record, llvm::StringRef name);
  ~JFSTimerStat();
  void printYAML(llvm::ScopedPrinter& os) const override;
  static bool classof(const JFSStat* s) { return s->getKind() == SINGLE_TIMER; }
};

class JFSAggregateTimerStat : public JFSStat {
private:
  std::list<std::unique_ptr<const JFSTimerStat>> timers;

public:
  JFSAggregateTimerStat(llvm::StringRef name);
  ~JFSAggregateTimerStat();
  void append(std::unique_ptr<JFSTimerStat> t);
  void clear();
  void printYAML(llvm::ScopedPrinter& os) const override;
  static bool classof(const JFSStat* s) {
    return s->getKind() == AGGREGATE_TIMER;
  }
};
}
}
#endif
