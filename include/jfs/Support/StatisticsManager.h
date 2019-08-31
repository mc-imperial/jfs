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
#ifndef JFS_SUPPORT_STATISTICS_MANAGER_H
#define JFS_SUPPORT_STATISTICS_MANAGER_H
#include "llvm/Support/raw_ostream.h"
#include <memory>

namespace jfs {
namespace support {

class JFSStat;
class StatisticsManagerImpl;
class StatisticsManager {
private:
  const std::unique_ptr<StatisticsManagerImpl> impl;

public:
  // FIXME: Figure out how to add iterators without leaking
  // implementation details
  StatisticsManager();
  ~StatisticsManager();
  void append(std::unique_ptr<JFSStat> stat);
  void clear();
  size_t size() const;
  void printYAML(llvm::raw_ostream& os) const;
  void dump() const;
};
}
}

#endif
