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
#include "jfs/Support/StatisticsManager.h"
#include "jfs/Support/JFSStat.h"
#include <assert.h>
#include <list>
#include <memory>

namespace jfs {
namespace support {

class StatisticsManagerImpl {
private:
  std::list<std::unique_ptr<const JFSStat>> stats;

public:
  StatisticsManagerImpl() {}
  ~StatisticsManagerImpl() {}
  void append(std::unique_ptr<JFSStat> stat) {
    assert(stat.get() != nullptr);
    stats.push_back(std::move(stat));
  }
  void clear() { stats.clear(); }
  size_t size() const { return stats.size(); }
  void printYAML(llvm::raw_ostream& os) const {
    llvm::ScopedPrinter sp(os);
    sp.getOStream() << "stats:";

    if (stats.size() == 0) {
      sp.getOStream() << "[]\n";
      return;
    }
    sp.getOStream() << "\n";

    sp.indent();
    for (const auto& stat : stats) {
      sp.printIndent();
      sp.getOStream() << "-";
      stat->printYAML(sp);
    }
    sp.unindent();
  }
  void dump() const { printYAML(llvm::errs()); }
};

StatisticsManager::StatisticsManager() : impl(new StatisticsManagerImpl()) {}

StatisticsManager::~StatisticsManager() {}

void StatisticsManager::append(std::unique_ptr<JFSStat> stat) {
  impl->append(std::move(stat));
}

void StatisticsManager::clear() { impl->clear(); }

size_t StatisticsManager::size() const { return impl->size(); }

void StatisticsManager::printYAML(llvm::raw_ostream& os) const {
  return impl->printYAML(os);
}

void StatisticsManager::dump() const { impl->dump(); }
}
}
