######################################################################################
### Unit tests
######################################################################################

# ut-cartesianProduct, ut-simpleUpperBound and ut-computeBetaMax are empty
# shells from an earlier design (their bodies are commented out). They are kept
# until the tests are rewritten with a test framework.
set(ZS_UNIT_TESTS
    ut-combiGenerator
    ut-cartesianProduct
    ut-simpleUpperBound
    ut-computeBetaMax
    ut-powerSetGenerator
    ut-paretoExtraction)

foreach(test ${ZS_UNIT_TESTS})
    add_executable(${test} ${test}.cpp)
    target_link_libraries(${test} PRIVATE zeno_legacy zeno_build_settings)
    add_test(NAME ${test} COMMAND ${test})
endforeach()

add_executable(ut-pddl ut-pddl.cpp)
target_link_libraries(ut-pddl PRIVATE zeno zeno_build_settings)
target_compile_definitions(ut-pddl PRIVATE ZS_PDDL_DIR="${PROJECT_SOURCE_DIR}/pddl")
add_test(NAME ut-pddl COMMAND ut-pddl)

# Performance test: unbounded runtime and always returns 1, so it is built but
# not registered with CTest.
add_executable(pt-powerSetGenerator pt-powerSetGenerator.cpp)
target_link_libraries(pt-powerSetGenerator PRIVATE zeno_legacy zeno_build_settings)

######################################################################################
### Exact solver (zeno_core)
######################################################################################

# Differential tests against the enumeration oracle (tests/oracle/partitionEnum.hpp).
add_executable(ut-zeno-core ut-zeno-core.cpp)
target_link_libraries(ut-zeno-core PRIVATE zeno::core zeno_build_settings)
target_include_directories(ut-zeno-core PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
add_test(NAME ut-zeno-core COMMAND ut-zeno-core)
set_tests_properties(ut-zeno-core PROPERTIES TIMEOUT 600)

######################################################################################
### Brute-force oracle
######################################################################################

add_executable(zenoOracle oracle/main.cpp)
target_link_libraries(zenoOracle PRIVATE zeno_legacy zeno_build_settings)

# The oracle header shares no code with the library, and neither does its test.
add_executable(ut-oracle ut-oracle.cpp)
target_link_libraries(ut-oracle PRIVATE zeno_build_settings)
add_test(NAME ut-oracle COMMAND ut-oracle)

######################################################################################
### Golden Pareto fronts: every solver variant against the brute-force oracle
######################################################################################
#
# golden/instances.txt lists the instances, golden/fronts holds the fronts
# produced by the oracle. golden/known-bugs.txt lists the "<target> <instance>"
# pairs that currently fail: they are registered with WILL_FAIL so the suite
# stays green, and they start failing as soon as the bug is fixed, so the entry
# has to be removed with the fix.

set(ZS_GOLDEN_DIR ${CMAKE_CURRENT_SOURCE_DIR}/golden)
set(ZS_GOLDEN_TARGETS zeno zenoSolver zenoSolver_naive zenoSolver_noDuplicate)

# Reconfigure when the lists change.
set_property(DIRECTORY APPEND PROPERTY CMAKE_CONFIGURE_DEPENDS
    ${ZS_GOLDEN_DIR}/instances.txt ${ZS_GOLDEN_DIR}/known-bugs.txt)

file(STRINGS ${ZS_GOLDEN_DIR}/known-bugs.txt ZS_KNOWN_BUGS REGEX "^[^#]")
file(STRINGS ${ZS_GOLDEN_DIR}/instances.txt ZS_GOLDEN_LINES REGEX "^[^#].*\\|")

foreach(line ${ZS_GOLDEN_LINES})
    string(REPLACE "|" ";" fields "${line}")
    list(GET fields 0 name)
    list(GET fields 1 args)
    string(REPLACE "@DATA@" "${ZS_GOLDEN_DIR}/data" args "${args}")
    string(STRIP "${args}" args)
    string(REGEX REPLACE " +" "|" args "${args}")
    set(expected ${ZS_GOLDEN_DIR}/fronts/${name}.front)

    # The oracle must reproduce the committed fronts.
    add_test(NAME golden/zenoOracle/${name}
        COMMAND ${CMAKE_COMMAND} -DEXE=$<TARGET_FILE:zenoOracle> -DARGS=${args}
                -DEXPECTED=${expected} -P ${ZS_GOLDEN_DIR}/checkFront.cmake)
    set_tests_properties(golden/zenoOracle/${name} PROPERTIES LABELS "golden;oracle" TIMEOUT 300)

    foreach(target ${ZS_GOLDEN_TARGETS})
        set(test golden/${target}/${name})
        add_test(NAME ${test}
            COMMAND ${CMAKE_COMMAND} -DEXE=$<TARGET_FILE:${target}> -DARGS=${args}
                    -DEXPECTED=${expected} -P ${ZS_GOLDEN_DIR}/checkFront.cmake)
        set_tests_properties(${test} PROPERTIES LABELS "golden" TIMEOUT 300)
        list(FIND ZS_KNOWN_BUGS "${target} ${name}" known)
        if(NOT known EQUAL -1)
            set_tests_properties(${test} PROPERTIES WILL_FAIL TRUE LABELS "golden;known-bug")
        endif()
    endforeach()
endforeach()
