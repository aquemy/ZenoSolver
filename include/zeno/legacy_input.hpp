#pragma once

#include <zeno/instance.hpp>

#include <optional>
#include <string>
#include <vector>

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
/// the order of the cities, which leaves the front unchanged. Two exceptions:
///  - the 2016 code swapped only when d[0] > d[1]. When truncation ties the
///    first two durations (-n 10 -D 1 -r 1 starts with d = (2, 2, ...)), the
///    2016 flags already mean the same as here and must not be translated;
///    `zeno generate` on both forms shows which case applies;
///  - zeno scales both duration sides of -E/-W with -l/-m, so the -E/-W
///    translation is exact only when the 2016 instance had the same -j/-k as
///    -l/-m (the defaults qualify); otherwise, write it as a data file.
struct Options
{
    int n = 3, t = 3, p = 2;
    /// -d: 2 lines (d, c) or 3 lines (d, dbar, c), optionally followed by a
    /// line "central" and the n rows of the central-flight table.
    std::optional<std::string> dataFile;
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
/// Unlike the 2016 solvers it accepts t = p. A data file's central-flight
/// table is multiplied by -r and truncated like the other values; without
/// one, the instance has the default table (Instance::central).
[[nodiscard]] Instance buildInstance(const Options& options);

/// The costs of the generator, c_i = x f(j i + k) + y for i = 1..n (-C -j -k
/// -x -y), multiplied by `adjust` and truncated toward zero, as in
/// buildInstance with adjust = -r.
[[nodiscard]] std::vector<Cost> generatedCosts(const Options& options, double adjust);
} // namespace zeno::legacy
