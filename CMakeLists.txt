cmake_minimum_required(VERSION 2.8)

set(CMAKE_INSTALL_RPATH_USE_LINK_PATH true)

set(release false)

if (release)
  set(CMAKE_C_FLAGS "-O3")
  set(CMAKE_CXX_FLAGS "-O3 -std=c++11")
else()
  set(CMAKE_C_FLAGS "-O0 -g")
  set(CMAKE_CXX_FLAGS "-O0 -g -std=c++11")
endif()

set(CMAKE_C_FLAGS "${CMAKE_C_FLAGS} -Wall -Wextra -std=c99")
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -Wall -Wextra -std=c++11")

find_package(osl REQUIRED)
find_package(clay REQUIRED)

include_directories("${CMAKE_CURRENT_SOURCE_DIR}/include")

include_directories(${OSL_INCLUDE_DIR})
include_directories(${CLAY_INCLUDE_DIR})

#file(GLOB_RECURSE
#     sources
#     ${CMAKE_CURRENT_SOURCE_DIR}/*)
add_executable(chlore "${CMAKE_CURRENT_SOURCE_DIR}/whiteboxing.cc")
target_link_libraries(chlore ${OSL_LIBRARY})
target_link_libraries(chlore ${CLAY_LIBRARY})
