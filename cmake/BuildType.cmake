######################################################################################
### 1) Define flags depending on the build type
######################################################################################
#-Wall -Wextra -ansi -pedantic -Werror
set(ZS_CXX_FLAGS " -std=c++11" CACHE STRING "General flags." FORCE)
set(ZS_CXX_FLAGS_DEBUG "-O0 -g" CACHE STRING "Flags for debug build." FORCE)
set(ZS_CXX_FLAGS_RELEASE "-O3" CACHE STRING "Flags for release build." FORCE)
set(ZS_CXX_FLAGS_PROFILING "-pg --coverage" CACHE STRING "Flags for profiling build." FORCE)
set(ZS_CXX_FLAGS_PARALLEL "-fopenmp -lpthread" CACHE STRING "Flags for parallel build." FORCE)

######################################################################################
### 2) Set flags to CMake
######################################################################################

if(ZS_PARALLEL)
    set(ZS_CXX_FLAGS "${ZS_CXX_FLAGS} ${ZS_CXX_FLAGS_PARALLEL}")
endif()

set(CMAKE_CXX_FLAGS ${ZS_CXX_FLAGS})
set(CMAKE_CXX_FLAGS_DEBUG "${ZS_CXX_FLAGS} ${ZS_CXX_FLAGS_DEBUG}")
set(CMAKE_CXX_FLAGS_RELEASE "${ZS_CXX_FLAGS} ${ZS_CXX_FLAGS_RELEASE}")
    
if(CMAKE_BUILD_TYPE STREQUAL "Profiling")
    set(CMAKE_CXX_FLAGS_DEBUG "${ZS_CXX_FLAGS} ${ZS_CXX_FLAGS_PROFILING}")
    set(ZS_GENERATE_TESTS TRUE)
endif()


