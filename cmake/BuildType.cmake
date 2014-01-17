######################################################################################
### 0) Define build types : Standard, Debug, Release, Profiling
######################################################################################

SET_PROPERTY(CACHE ZS_BUILD_TYPE PROPERTY STRINGS Standard Debug Release Profiling)

######################################################################################
### 1) Define flags depending on the build type
######################################################################################

set(ZS_CXX_FLAGS "-Wall -Wextra -ansi -pedantic -Werror -std=c++11" CACHE STRING "General flags." FORCE)
set(ZS_CXX_FLAGS_DEBUG "-O0 -g" CACHE STRING "Flags for debug build." FORCE)
set(ZS_CXX_FLAGS_RELEASE "-O3" CACHE STRING "Flags for release build." FORCE)
set(ZS_CXX_FLAGS_PROFILING "-pg --coverage" CACHE STRING "Flags for profiling build." FORCE)
set(ZS_CXX_FLAGS_PARALLEL "-fopenmp -D_GLIBCXX_PARALLEL" CACHE STRING "Flags for parallel build." FORCE)

######################################################################################
### 2) Set flags to CMake
######################################################################################

if(ZS_PARALLEL)
    set(ZS_CXX_FLAGSS ${ZS_CXX_FLAGS} ${ZS_CXX_FLAGS_PARALLEL})
endif()

if(ZS_BUILD_TYPE STREQUAL "Standard")
    set(CMAKE_CXX_FLAGS ${ZS_CXX_FLAGS})
elseif(ZS_BUILD_TYPE STREQUAL "Debug")
    set(CMAKE_BUILD_TYPE Debug)
    set(CMAKE_CXX_FLAGS_DEBUG "${ZS_CXX_FLAGS} ${ZS_CXX_FLAGS_DEBUG}")
elseif(ZS_BUILD_TYPE STREQUAL "Release")
    set(CMAKE_BUILD_TYPE Release)
    set(CMAKE_CXX_FLAGS_RELEASE "${ZS_CXX_FLAGS} ${ZS_CXX_FLAGS_RELEASE}")
elseif(ZS_BUILD_TYPE STREQUAL "Profiling")
    set(CMAKE_BUILD_TYPE Debug)
    set(CMAKE_CXX_FLAGS_DEBUG "${ZS_CXX_FLAGS} ${ZS_CXX_FLAGS_DEBUG} ${ZS_CXX_FLAGS_PROFILING}")
    set(ZS_GENERATE_TESTS TRUE)
endif()


