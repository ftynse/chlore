project(chlore)
cmake_minimum_required(VERSION 3.0)

set(CMAKE_INSTALL_RPATH_USE_LINK_PATH true)

set(CMAKE_C_FLAGS_DEBUG "-g -Wall -Wextra -pedantic -O0 -std=c99")
set(CMAKE_CXX_FLAGS_DEBUG "-g -Wall -Wextra -pedantic -O0 -std=c++11")
set(CMAKE_C_FLAGS_RELEASE "-Wall -Wextra -O3 -std=c99")
set(CMAKE_CXX_FLAGS_RELEASE "-Wall -Wextra -O3 -std=c++11")
set(CMAKE_C_FLAGS "-Wall -Wextra -std=c99")
set(CMAKE_CXX_FLAGS "-Wall -Wextra -std=c++11")

find_package(osl REQUIRED)
find_package(clay REQUIRED)
find_package(cloog-isl REQUIRED)

include_directories("${CMAKE_CURRENT_SOURCE_DIR}/include")

include_directories(${OSL_INCLUDE_DIR})
include_directories(${CLAY_INCLUDE_DIR})
include_directories(${CLOOG_ISL_INCLUDE_DIR})

set(library_files "${CMAKE_CURRENT_SOURCE_DIR}/whiteboxing.cc"
                  "${CMAKE_CURRENT_SOURCE_DIR}/tree.cc"
                  "${CMAKE_CURRENT_SOURCE_DIR}/beta_uncover.cc")

file(GLOB include_files "include/*.h")
file(GLOB header_files "*.h")

add_library(chlore_obj
            OBJECT
            ${library_files} ${include_files} ${header_files})

add_executable(chlore "${CMAKE_CURRENT_SOURCE_DIR}/chlore.cc"
                      $<TARGET_OBJECTS:chlore_obj>)
target_link_libraries(chlore ${OSL_LIBRARY})
target_link_libraries(chlore ${CLAY_LIBRARY})
target_link_libraries(chlore ${CLOOG_ISL_LIBRARY})

add_library(libchlore
            SHARED
            $<TARGET_OBJECTS:chlore_obj>)
set_target_properties(libchlore PROPERTIES OUTPUT_NAME chlore)
target_link_libraries(libchlore ${OSL_LIBRARY})
target_link_libraries(libchlore ${CLAY_LIBRARY})
target_link_libraries(libchlore ${CLOOG_ISL_LIBRARY})

add_library(libchlorea
            STATIC
            $<TARGET_OBJECTS:chlore_obj>)
set_target_properties(libchlorea PROPERTIES OUTPUT_NAME chlore)
target_link_libraries(libchlorea ${OSL_LIBRARY})
target_link_libraries(libchlorea ${CLAY_LIBRARY})
target_link_libraries(libchlorea ${CLOOG_ISL_LIBRARY})

install(TARGETS chlore RUNTIME DESTINATION bin)
install(TARGETS libchlore LIBRARY DESTINATION lib)
install(TARGETS libchlorea ARCHIVE DESTINATION lib)
install(DIRECTORY include/ DESTINATION include FILES_MATCHING PATTERN "*.h")
install(FILES chlore-config.cmake DESTINATION lib/chlore)

configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake-uninstall.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmake-uninstall.cmake"
    IMMEDIATE @ONLY)

add_custom_target(uninstall
    COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake-uninstall.cmake)

