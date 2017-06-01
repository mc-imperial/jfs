jfs_add_component(JFSCore
  JFSContext.cpp
  Query.cpp
  SMTLIB2Parser.cpp
  Solver.cpp
  Z3Node.cpp
)
target_link_libraries(JFSCore PUBLIC "${Z3_LIBRARIES}")
