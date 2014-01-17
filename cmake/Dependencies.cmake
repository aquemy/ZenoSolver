######################################################################################
### 0) Check dependencies according to build and install type
######################################################################################

if(${ZS_GENERATE_DOC})
    include(FindDoxygen REQUIERED)
endif()

if(${ZS_PARALLEL})
    find_package(OpenMP)
endif()

if(${ZS_PLOT})
    include(FindGnuplot REQUIERED)
endif()
