#pragma once

#include <zeno/instance.hpp>

#include <vector>

namespace zeno
{
/// An instance reduced for the front computation.
///
/// - Dominance: a city j with d_i <= d_j, dbar_i <= dbar_j and c_i <= c_j for
///   another city i is never needed. Replacing every landing in j by a landing
///   in i keeps a partition admissible (merge the two parity columns: h'_k =
///   h_k,i xor h_k,j), keeps a role configuration balanced (merge the two
///   cities), and raises neither the cost nor a load. Equal cities are merged
///   the same way. For a symmetric instance the kept cities form a staircase:
///   d strictly increasing, c strictly decreasing.
/// - Scaling: durations are divided by their gcd g.
/// - Levels: a level T bounds every plane's load in level units, and a plan
///   at level T has makespan makespanPerLevel * T. Symmetric instances use
///   half-loads (a landing in city i weighs d_i, makespanPerLevel = 2g);
///   non-symmetric ones use full loads with role weights (makespanPerLevel =
///   g): a crossing C_I -> i -> C_G or back weighs d_i + dbar_i (fill), a
///   drop-off C_I -> i -> C_I weighs 2 d_i (drop), a pick-up C_G -> i -> C_G
///   weighs 2 dbar_i (pick). `low` = min over roles, the weight of lemma R.
struct ReducedInstance
{
    std::vector<Time> d;        ///< scaled C_I-side durations (strictly increasing when symmetric)
    std::vector<Time> dbar;     ///< scaled C_G-side durations (equal to d when symmetric)
    std::vector<Cost> c;        ///< costs (strictly decreasing when symmetric)
    std::vector<int> original;  ///< index of a representative original city
    std::vector<Time> fill, drop, pick, low; ///< role weights in level units
    std::vector<int> byDrop, byPick;          ///< cities by increasing drop / pick weight
    Time scale = 1;             ///< g
    Time makespanPerLevel = 2;  ///< 2g (symmetric) or g
    bool symmetric = true;
    int t = 0, p = 0;

    [[nodiscard]] int n() const noexcept { return static_cast<int>(d.size()); }
    [[nodiscard]] int landings() const noexcept { return 2 * t - p; }
    /// Largest number of landings a single plane can need: s - p + 1.
    [[nodiscard]] int maxGroup() const noexcept { return landings() - p + 1; }
    /// Upper bound on the planes of a useful link tree, min(p, t - p + 1)
    /// (a plan has at most t - p links).
    [[nodiscard]] int maxTree() const noexcept { return p < t - p + 1 ? p : t - p + 1; }
    /// Lower bound on the level of every plan: s landings, at least
    /// ceil(s / p) on some plane, each weighing at least min(low). Exact (the
    /// fastest point) for symmetric instances.
    [[nodiscard]] Time lowestLevel() const noexcept;
    /// Symmetric: the smallest level reaching the cheapest cost s * c_min,
    /// beyond which E is constant. Non-symmetric: a level at which forests
    /// reach s * c_min (all landings as crossings in the cheapest city).
    [[nodiscard]] Time highestLevel() const noexcept;
    /// Index of the cheapest city (the fastest among the cheapest).
    [[nodiscard]] int cheapest() const noexcept;
};

/// Requires a valid instance.
[[nodiscard]] ReducedInstance reduce(const Instance& instance);
} // namespace zeno
