#include "jfs/FuzzingCommon/EqualityExtractionPass.h"
#include "jfs/Core/SMTLIB2Parser.h"
#include "gtest/gtest.h"
#include <memory>

using namespace jfs::core;
using namespace jfs::fuzzingCommon;

class ParserHelper {
private:
  std::unique_ptr<JFSContext> ctx;
  std::unique_ptr<SMTLIB2Parser> parser;

public:
  ParserHelper() {
    JFSContextConfig ctxCfg;
    ctx.reset(new JFSContext(ctxCfg));
    parser.reset(new SMTLIB2Parser(*ctx));
  }
  JFSContext &getContext() { return *ctx; }
  SMTLIB2Parser &getParser() { return *parser; }
};

TEST(EqualityExtractionPass, singleEquality) {
  ParserHelper h;
  auto query = h.getParser().parseStr(
      R"(
    (declare-const a (_ BitVec 8))
    (declare-const b (_ BitVec 8))
    (assert (= a b))
    (assert (bvugt a #x03))
    )");
  ASSERT_EQ(h.getParser().getErrorCount(), 0UL);
  ASSERT_NE(query.get(), nullptr);
  ASSERT_EQ(query->constraints.size(), 2UL);
  EqualityExtractionPass eep;
  eep.run(*query);
  ASSERT_EQ(query->constraints.size(), 1UL);
  ASSERT_EQ(eep.equalities.size(), 1UL);
  auto es = *(eep.equalities.cbegin());
  // Expect that a and b are in equality set
  ASSERT_EQ(es->size(), 2UL);
  bool foundA = false;
  bool foundB = false;
  for (const auto &e : *es) {
    if (e.toStr() == "a")
      foundA = true;
    if (e.toStr() == "b")
      foundB = true;
  }
  ASSERT_TRUE(foundA);
  ASSERT_TRUE(foundB);
  // Check that remaining constraints are as expected
  ASSERT_EQ(query->constraints[0].toStr(), "(bvugt a #x03)");
}

TEST(EqualityExtractionPass, ThreeEqualVars) {
  ParserHelper h;
  auto query = h.getParser().parseStr(
      R"(
    (declare-const a (_ BitVec 8))
    (declare-const b (_ BitVec 8))
    (declare-const c (_ BitVec 8))
    (assert (= a b))
    (assert (= b c))
    ; these are redundant equalities that should be removed by pass
    (assert (= a c))
    (assert (= b a))
    (assert (= c a))
    (assert (= a c))
    (assert (bvugt a #x03))
    )");
  ASSERT_EQ(h.getParser().getErrorCount(), 0UL);
  ASSERT_NE(query.get(), nullptr);
  ASSERT_EQ(query->constraints.size(), 7UL);
  EqualityExtractionPass eep;
  eep.run(*query);
  ASSERT_EQ(query->constraints.size(), 1UL);
  ASSERT_EQ(eep.equalities.size(), 1UL);
  auto es = *(eep.equalities.cbegin());
  // Expect that a, b, and c are in equality set
  ASSERT_EQ(es->size(), 3UL);
  bool foundA = false;
  bool foundB = false;
  bool foundC = false;
  for (const auto &e : *es) {
    if (e.toStr() == "a") {
      foundA = true;
      continue;
    }
    if (e.toStr() == "b") {
      foundB = true;
      continue;
    }
    if (e.toStr() == "c") {
      foundC = true;
      continue;
    }
  }
  ASSERT_TRUE(foundA);
  ASSERT_TRUE(foundB);
  ASSERT_TRUE(foundC);
  // Check that remaining constraints are as expected
  ASSERT_EQ(query->constraints[0].toStr(), "(bvugt a #x03)");
}
