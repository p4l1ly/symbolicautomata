cmake_minimum_required(VERSION 3.17)

project(
  boolafaRpc
  VERSION 0.1.0
  DESCRIPTION "CapnProto Rpc for the boolafa.BoolAfa benchmark"
  LANGUAGES CXX
)

find_package(CapnProto REQUIRED)
find_library(AutomataSafaCapnp automata-safa-capnp REQUIRED)
find_path(AutomataSafaCapnpInclude automata-safa-capnp REQUIRED)

find_package(JNI)

add_library(
  boolafaRpc
  SHARED
  src/main/native/src/boolafa_BoolAfa.cpp
)
target_include_directories(
  boolafaRpc
  PRIVATE
  "${AutomataSafaCapnpInclude}"
  src/main/native/include
  "${JNI_INCLUDE_DIRS}"
)
target_link_libraries(
  boolafaRpc
  PRIVATE
  "${JNI_LIBRARIES}"
  CapnProto::capnp
  CapnProto::capnp-rpc
  "${AutomataSafaCapnp}"
)
set_property(TARGET boolafaRpc PROPERTY CXX_STANDARD 20)
