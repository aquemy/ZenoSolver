#pragma once

#include <zeno/instance.hpp>

#include <optional>
#include <string>

namespace zeno::legacy
{
/// The instance options of the 2016 solvers (`zenoSolver -h`). Building an
/// instance from them reproduces the 2016 construction exactly, quirks
/// included, so that both solvers see the same data:
/// - values are multiplied by `adjust` (-r) and truncated toward zero;
/// - if d[0] > d[1] after that, the duration and cost vectors are swapped and
///   the east durations reversed (the 2016 code assumed increasing durations).
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
/// Unlike the 2016 solvers it accepts t = p. When `swapped` is given, it tells
/// whether the 2016 swap of durations and costs (d[0] > d[1]) was applied.
[[nodiscard]] Instance buildInstance(const Options& options, bool* swapped = nullptr);
} // namespace zeno::legacy
