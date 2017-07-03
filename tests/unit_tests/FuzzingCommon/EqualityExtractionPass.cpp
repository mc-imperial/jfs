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

TEST(EqualityExtractionPass, boolAssignmentTrue) {
  ParserHelper h;
  auto query = h.getParser().parseStr(
      R"(
    (declare-const a Bool)
    (assert a)
    )");
  ASSERT_EQ(h.getParser().getErrorCount(), 0UL);
  ASSERT_NE(query.get(), nullptr);
  ASSERT_EQ(query->constraints.size(), 1UL);
  EqualityExtractionPass eep;
  eep.run(*query);
  ASSERT_EQ(query->constraints.size(), 0UL);
  ASSERT_EQ(eep.equalities.size(), 1UL);
  auto es = *(eep.equalities.cbegin());
  // Expect that a and true
  ASSERT_EQ(es->size(), 2UL);
  bool foundA = false;
  bool foundTrue = false;
  for (const auto& e : *es) {
    if (e.toStr() == "a")
      foundA = true;
    if (e.isTrue())
      foundTrue = true;
  }
  ASSERT_TRUE(foundA);
  ASSERT_TRUE(foundTrue);
}

TEST(EqualityExtractionPass, boolAssignmentFalse) {
  ParserHelper h;
  auto query = h.getParser().parseStr(
      R"(
    (declare-const a Bool)
    (assert (not a))
    )");
  ASSERT_EQ(h.getParser().getErrorCount(), 0UL);
  ASSERT_NE(query.get(), nullptr);
  ASSERT_EQ(query->constraints.size(), 1UL);
  EqualityExtractionPass eep;
  eep.run(*query);
  ASSERT_EQ(query->constraints.size(), 0UL);
  ASSERT_EQ(eep.equalities.size(), 1UL);
  auto es = *(eep.equalities.cbegin());
  // Expect that a and false
  ASSERT_EQ(es->size(), 2UL);
  bool foundA = false;
  bool foundFalse = false;
  for (const auto& e : *es) {
    if (e.toStr() == "a")
      foundA = true;
    if (e.isFalse())
      foundFalse = true;
  }
  ASSERT_TRUE(foundA);
  ASSERT_TRUE(foundFalse);
}

TEST(EqualityExtractionPass, singleInconsistency) {
  ParserHelper h;
  auto query = h.getParser().parseStr(
      R"(
    (declare-const a (_ BitVec 8))
    (assert (= a #x03))
    (assert (= a #x04))
    )");
  ASSERT_EQ(h.getParser().getErrorCount(), 0UL);
  ASSERT_NE(query.get(), nullptr);
  ASSERT_EQ(query->constraints.size(), 2UL);
  EqualityExtractionPass eep;
  eep.run(*query);
  ASSERT_EQ(query->constraints.size(), 1UL);
  ASSERT_EQ(eep.equalities.size(), 1UL);
  auto es = *(eep.equalities.cbegin());
  // Expect that a, #x03, and #x04 are in equality set
  ASSERT_EQ(es->size(), 3UL);
  bool foundA = false;
  bool found3 = false;
  bool found4 = false;
  for (const auto& e : *es) {
    if (e.toStr() == "a")
      foundA = true;
    if (e.isConstant()) {
      uint64_t value = 0;
      bool success = e.asApp().getConstantAsUInt64(&value);
      ASSERT_TRUE(success);
      if (value == UINT64_C(3))
        found3 = true;
      if (value == UINT64_C(4))
        found4 = true;
    }
  }
  ASSERT_TRUE(foundA);
  ASSERT_TRUE(found3);
  ASSERT_TRUE(found4);
  // Check that the constraints got replaced with false
  ASSERT_EQ(query->constraints.size(), UINT64_C(1));
  ASSERT_TRUE(query->constraints[0].isFalse());
}

TEST(EqualityExtractionPass, mergeSets) {
  ParserHelper h;
  auto query = h.getParser().parseStr(
      R"(
    (declare-const a Bool)
    (declare-const b Bool)
    (declare-const c Bool)
    (declare-const d Bool)
    ; The transitive closure of equalities
    ; should be a single set
    (assert (= a b))
    (assert (= c d))
    (assert (= a c))
    )");
  ASSERT_EQ(h.getParser().getErrorCount(), 0UL);
  ASSERT_NE(query.get(), nullptr);
  ASSERT_EQ(query->constraints.size(), 3UL);
  EqualityExtractionPass eep;
  eep.run(*query);
  ASSERT_EQ(query->constraints.size(), 0UL);
  ASSERT_EQ(eep.equalities.size(), 1UL);
  auto es = *(eep.equalities.cbegin());
  // Expect that a,b,c,d
  ASSERT_EQ(es->size(), 4UL);
  bool foundA = false;
  bool foundB = false;
  bool foundC = false;
  bool foundD = false;
  for (const auto& e : *es) {
    if (e.toStr() == "a")
      foundA = true;
    if (e.toStr() == "b")
      foundB = true;
    if (e.toStr() == "c")
      foundC = true;
    if (e.toStr() == "d")
      foundD = true;
  }
  ASSERT_TRUE(foundA);
  ASSERT_TRUE(foundB);
  ASSERT_TRUE(foundC);
  ASSERT_TRUE(foundD);
}
