# Run EXE with ARGS (words separated by '|') plus -F and compare its stdout,
# the Pareto front as "cost makespan" lines, with the EXPECTED file.
# Usage: cmake -DEXE=... -DARGS=... -DEXPECTED=... -P checkFront.cmake
string(REPLACE "|" ";" arguments "${ARGS}")
execute_process(
    COMMAND "${EXE}" ${arguments} -F
    OUTPUT_VARIABLE actual
    ERROR_VARIABLE errors
    RESULT_VARIABLE status)
if(NOT status EQUAL 0)
    message(FATAL_ERROR "${EXE} exited with '${status}'\n${errors}")
endif()
file(READ "${EXPECTED}" expected)
if(NOT actual STREQUAL expected)
    message(FATAL_ERROR "Pareto front mismatch for ${EXE} ${arguments}\n"
                        "expected (cost makespan):\n${expected}\nactual:\n${actual}")
endif()
