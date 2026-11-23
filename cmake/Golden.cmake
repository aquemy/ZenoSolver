######################################################################################
### Golden Pareto fronts: every solver variant against the brute-force oracle
######################################################################################
#
# tests/golden/instances.txt lists the instances, tests/golden/fronts holds the
# fronts produced by the oracle. tests/golden/known-bugs.txt lists the
# "<target> <instance>" pairs that currently fail: they are registered with
# WILL_FAIL so the suite stays green, and they start failing as soon as the bug
# is fixed, so the entry has to be removed with the fix.

set(ZS_GOLDEN_DIR ${CMAKE_SOURCE_DIR}/tests/golden)
set(ZS_GOLDEN_TARGETS zenoSolver zenoSolver_naive zenoSolver_noDuplicate)

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
    set_tests_properties(golden/zenoOracle/${name} PROPERTIES LABELS "golden;oracle" TIMEOUT 120)

    foreach(target ${ZS_GOLDEN_TARGETS})
        set(test golden/${target}/${name})
        add_test(NAME ${test}
            COMMAND ${CMAKE_COMMAND} -DEXE=$<TARGET_FILE:${target}> -DARGS=${args}
                    -DEXPECTED=${expected} -P ${ZS_GOLDEN_DIR}/checkFront.cmake)
        set_tests_properties(${test} PROPERTIES LABELS "golden" TIMEOUT 120)
        list(FIND ZS_KNOWN_BUGS "${target} ${name}" known)
        if(NOT known EQUAL -1)
            set_tests_properties(${test} PROPERTIES WILL_FAIL TRUE LABELS "golden;known-bug")
        endif()
    endforeach()
endforeach()
