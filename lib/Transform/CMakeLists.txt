jfs_add_component(JFSTransform
  AndHoistingPass.cpp
  DuplicateConstraintEliminationPass.cpp
  QueryPassManager.cpp
  SimplificationPass.cpp
  StandardPasses.cpp
  TrueConstraintEliminationPass.cpp
)
target_link_libraries(JFSTransform PUBLIC JFSCore)
