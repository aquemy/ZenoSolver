# Run EXE with ARGS (words separated by '|') and --certificate CERT, then
# 'EXE check CERT', which must accept it.
# Usage: cmake -DEXE=... -DARGS=... -DCERT=... -P checkCertificate.cmake
string(REPLACE "|" ";" arguments "${ARGS}")
get_filename_component(dir "${CERT}" DIRECTORY)
file(MAKE_DIRECTORY "${dir}")
execute_process(
    COMMAND "${EXE}" ${arguments} --certificate "${CERT}"
    OUTPUT_QUIET
    ERROR_VARIABLE errors
    RESULT_VARIABLE status)
if(NOT status EQUAL 0)
    message(FATAL_ERROR "${EXE} exited with '${status}'\n${errors}")
endif()
execute_process(
    COMMAND "${EXE}" check "${CERT}"
    OUTPUT_VARIABLE report
    RESULT_VARIABLE status)
if(NOT status EQUAL 0)
    message(FATAL_ERROR "certificate rejected:\n${report}")
endif()
message(STATUS "${report}")
