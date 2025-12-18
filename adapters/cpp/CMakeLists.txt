cmake_minimum_required(VERSION 3.16)
project(veribiota_streaming_adapter CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

set(
  VERIBIOTA_CHECKS_LIB
  ""
  CACHE FILEPATH
  "Path to libbiosim_checks built from engine/biosim-checks (e.g. .../target/release/deps/libbiosim_checks.so)"
)

if(NOT VERIBIOTA_CHECKS_LIB AND DEFINED ENV{VERIBIOTA_CHECKS_LIB})
  set(
    VERIBIOTA_CHECKS_LIB
    "$ENV{VERIBIOTA_CHECKS_LIB}"
    CACHE FILEPATH
    "Path to libbiosim_checks built from engine/biosim-checks (e.g. .../target/release/deps/libbiosim_checks.so)"
    FORCE
  )
endif()

if(NOT VERIBIOTA_CHECKS_LIB)
  set(_VERIBIOTA_CHECKS_LIB_HINTS
    "${CMAKE_CURRENT_LIST_DIR}/../../engine/biosim-checks/target/release"
    "${CMAKE_CURRENT_LIST_DIR}/../../engine/biosim-checks/target/release/deps"
    "${CMAKE_CURRENT_LIST_DIR}/../../engine/biosim-checks/target/debug"
    "${CMAKE_CURRENT_LIST_DIR}/../../engine/biosim-checks/target/debug/deps"
    "${CMAKE_CURRENT_LIST_DIR}/../../target/release"
    "${CMAKE_CURRENT_LIST_DIR}/../../target/release/deps"
    "${CMAKE_CURRENT_LIST_DIR}/../../target/debug"
    "${CMAKE_CURRENT_LIST_DIR}/../../target/debug/deps"
  )
  find_library(
    _VERIBIOTA_CHECKS_LIB_FOUND
    NAMES biosim_checks
    HINTS ${_VERIBIOTA_CHECKS_LIB_HINTS}
    NO_DEFAULT_PATH
  )
  if(_VERIBIOTA_CHECKS_LIB_FOUND)
    set(
      VERIBIOTA_CHECKS_LIB
      "${_VERIBIOTA_CHECKS_LIB_FOUND}"
      CACHE FILEPATH
      "Path to libbiosim_checks built from engine/biosim-checks (e.g. .../target/release/deps/libbiosim_checks.so)"
      FORCE
    )
    message(STATUS "Auto-detected VERIBIOTA_CHECKS_LIB=${VERIBIOTA_CHECKS_LIB}")
  endif()
endif()

if(NOT VERIBIOTA_CHECKS_LIB)
  message(
    FATAL_ERROR
    "Set VERIBIOTA_CHECKS_LIB to the path of libbiosim_checks (built from engine/biosim-checks).\n"
    "Hint:\n"
    "  cargo build --manifest-path engine/biosim-checks/Cargo.toml --release\n"
    "  cmake -S adapters/cpp -B adapters/cpp/build -DCMAKE_BUILD_TYPE=Release \\\n"
    "    -DVERIBIOTA_CHECKS_LIB=$PWD/engine/biosim-checks/target/release/deps/libbiosim_checks.so\n"
  )
endif()

add_executable(streaming_adapter main.cpp)
target_include_directories(streaming_adapter PRIVATE ${CMAKE_CURRENT_LIST_DIR}/../../engine/biosim-checks/ffi)
target_link_libraries(streaming_adapter PRIVATE ${VERIBIOTA_CHECKS_LIB})
