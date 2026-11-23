#pragma once

#include <zeno/instance.hpp>

#include <vector>

namespace zeno
{
/// A symmetric instance reduced for the front computation.
///
/// - Dominance: a city j with d_i <= d_j and c_i <= c_j for another city i is
///   never needed. Replacing every landing in j by a landing in i keeps a
///   partition admissible (merge the two parity columns: h'_k = h_k,i xor
///   h_k,j), and lowers neither the cost nor a load. Equal cities are merged
///   the same way. The kept cities form a staircase: d strictly increasing,
///   c strictly decreasing.
/// - Scaling: durations are divided by their gcd g, so the solver's half
///   makespan T is in units of g and a makespan is 2 g T.
struct ReducedInstance
{
    std::vector<Time> d;        ///< scaled durations, strictly increasing
    std::vector<Cost> c;        ///< costs, strictly decreasing
    std::vector<int> original;  ///< index of a representative original city
    Time scale = 1;             ///< g
    int t = 0, p = 0;

    [[nodiscard]] int n() const noexcept { return static_cast<int>(d.size()); }
    [[nodiscard]] int landings() const noexcept { return 2 * t - p; }
    /// Largest number of landings a single plane can need: s - p + 1.
    [[nodiscard]] int maxGroup() const noexcept { return landings() - p + 1; }
    /// Upper bound on the planes of a useful link tree, min(p, t - p + 1).
    [[nodiscard]] int maxTree() const noexcept { return p < t - p + 1 ? p : t - p + 1; }
    /// Smallest feasible T: every landing in the fastest city, balanced.
    [[nodiscard]] Time lowestLevel() const noexcept;
    /// Smallest T at which the cheapest cost s * c_min is reached; E is constant beyond.
    [[nodiscard]] Time highestLevel() const noexcept;
};

/// Requires a symmetric, valid instance.
[[nodiscard]] ReducedInstance reduce(const Instance& instance);
} // namespace zeno
