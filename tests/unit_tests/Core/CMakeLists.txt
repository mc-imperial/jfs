add_jfs_unit_test(Core
  FloatSpecialConstants.cpp
)
target_link_libraries(Core${UNIT_TEST_EXE_SUFFIX}
  PRIVATE
  JFSCore
)
