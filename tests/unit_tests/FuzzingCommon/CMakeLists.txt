# Just to check the build works
add_jfs_unit_test(FuzzingCommon
  EqualityExtractionPass.cpp
)
target_link_libraries(FuzzingCommon${UNIT_TEST_EXE_SUFFIX}
  PRIVATE
  JFSFuzzingCommon
  JFSCore
)
