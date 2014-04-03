ZenoSolver
==========

Optimal solver for multiobjectives ZenoTransportation problem.

# Requirements

CMake
g++ >= 4.7 for C++11 features.
(optional) doxygen for documentation

# How to compile

mkdir build && cd build
cmake ..
make -j

# Build & Compilation Options

By default the build is in Release mode, with all optimisations.
To activate the DEBUG build, in build folder, use:

cmake .. -DCMAKE_BUILD_TYPE=DEBUG
make

# RunTime Options

As ZenoSolver handles only integers for cost and durations, it will cast generated vectors (or provided data) to integers. The adjustement factor (option -r) is a multiplicative constant in order to avoid some errors (for instance, obtaining more than once the value 0 because log(i) and log(i+1) have same floor value.

By default it is set to 1 but a better value for most of functions could be 100.

More information using ./zenoSolver -h.

