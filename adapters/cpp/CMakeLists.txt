cmake_minimum_required(VERSION 3.16)
project(veribiota_streaming_adapter CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

if(NOT VERIBIOTA_CHECKS_LIB)
  message(FATAL_ERROR "Set VERIBIOTA_CHECKS_LIB to the path of libbiosim_checks (built from engine/biosim-checks).")
endif()

add_executable(streaming_adapter main.cpp)
target_include_directories(streaming_adapter PRIVATE ${CMAKE_CURRENT_LIST_DIR}/../../engine/biosim-checks/ffi)
target_link_libraries(streaming_adapter PRIVATE ${VERIBIOTA_CHECKS_LIB})
