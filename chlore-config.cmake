# Try to find the chlore library

# CHLORE_FOUND       - System has chlore lib
# CHLORE_INCLUDE_DIR - The chlore include directory
# CHLORE_LIBRARY     - Library needed to use chlore

if (CHLORE_INCLUDE_DIR AND CHLORE_LIBRARY)
        # Already in cache, be silent
        set(CHLORE_FIND_QUIETLY TRUE)
endif()

find_path(CHLORE_INCLUDE_DIR NAMES chlore/chlore.h)
find_library(CHLORE_LIBRARY NAMES chlore)

if (CHLORE_LIBRARY AND CHLORE_INCLUDE_DIR)
        message(STATUS "Library chlore found =) ${CHLORE_LIBRARY}")
else()
        message(STATUS "Library chlore not found =(")
endif()

include(FindPackageHandleStandardArgs)
FIND_PACKAGE_HANDLE_STANDARD_ARGS(CHLORE DEFAULT_MSG CHLORE_INCLUDE_DIR CHLORE_LIBRARY)

mark_as_advanced(CHLORE_INCLUDE_DIR CHLORE_LIBRARY)
