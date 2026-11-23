#pragma once

#include <zeno/types.hpp>

#include <compare>
#include <vector>

namespace zeno
{
/// A MultiZenoTravel instance: t passengers and p planes start in the initial
/// city C_I and must all end in the goal city C_G; there is no direct flight
/// between C_I and C_G. Central city i is reached from C_I in d[i], from C_G in
/// dbar[i], and every landing in it costs c[i]. Central-to-central flights are
/// assumed no faster than going through a hub (assumption A1 of the theory
/// note), which holds for every generated instance.
struct Instance
{
    std::vector<Time> d;    ///< durations C_I <-> i
    std::vector<Time> dbar; ///< durations C_G <-> i (equal to d when symmetric)
    std::vector<Cost> c;    ///< landing costs
    int t = 0;              ///< passengers
    int p = 0;              ///< planes

    [[nodiscard]] int n() const noexcept { return static_cast<int>(d.size()); }
    /// Minimum number of landings of a plan, 2t - p (counting lemma).
    [[nodiscard]] int landings() const noexcept { return 2 * t - p; }
    [[nodiscard]] bool symmetric() const { return d == dbar; }

    /// Throws std::invalid_argument unless 1 <= p <= t, n >= 1, the vectors have
    /// length n and every value is non-negative.
    void validate() const;
};

/// A point of the Pareto front.
struct FrontPoint
{
    Cost cost = 0;
    Time makespan = 0;
    auto operator<=>(const FrontPoint&) const = default;
};

/// Pareto front, sorted by increasing makespan (hence strictly decreasing cost).
using Front = std::vector<FrontPoint>;

/// Keeps the points not weakly dominated by another one (one point per
/// distinct objective vector), sorted by increasing makespan.
[[nodiscard]] Front paretoFilter(std::vector<FrontPoint> points);
} // namespace zeno
