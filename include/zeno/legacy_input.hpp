#pragma once

#include <zeno/instance.hpp>

#include <optional>
#include <string>

namespace zeno::legacy
{
/// The instance options of the 2016 solvers (`zenoSolver -h`), with their
/// generators: values are multiplied by `adjust` (-r) and truncated toward
/// zero, as in 2016. Each option means what it says: -C the costs, -D the
/// durations, -E the C_I-side and -W the C_G-side durations; data files are
/// read as written.
///
/// The 2016 solvers also swapped the duration and cost vectors (and reversed
/// the C_G-side durations) whenever d[0] > d[1], which their generator always
/// produced. zeno does not: a 2016 or paper instance "-C a -D b" is "-C b -D a"
/// here (and -j/-k with -l/-m), and "-C c -E a -W b" is "-C a -E c -W b", up to
/// the order of the cities, which leaves the front unchanged.
struct Options
{
    int n = 3, t = 3, p = 2;
    std::optional<std::string> dataFile; ///< -d: 2 lines (d, c) or 3 lines (d, dbar, c)
    int costFunction = 3;                ///< -C: 1 log, 2 sqrt, 3 identity, 4 2^i, 5 5(i/2) + 0.1(i%2)
    int durationFunction = 3;            ///< -D
    std::optional<int> eastFunction;     ///< -E (non-symmetric when -E and -W are both set)
    std::optional<int> westFunction;     ///< -W
    double adjust = 1;                   ///< -r
    double scaleC = 1, transC = 0;       ///< -j, -k: c_i = x f(j i + k) + y
    double scaleD = 1, transD = 0;       ///< -l, -m: d_i = x g(l (n + 1 - i) + m) + y
    double x = 1, y = 0;                 ///< -x, -y
};

/// Builds the instance; throws std::invalid_argument or std::runtime_error.
/// Unlike the 2016 solvers it accepts t = p.
[[nodiscard]] Instance buildInstance(const Options& options);
} // namespace zeno::legacy
