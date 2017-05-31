jfs_add_component(JFSTransform
  AndHoistingPass.cpp
  QueryPassManager.cpp
  SimplificationPass.cpp
  StandardPasses.cpp
)
target_link_libraries(JFSTransform PUBLIC JFSCore)
