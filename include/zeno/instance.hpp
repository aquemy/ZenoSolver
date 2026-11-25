#pragma once

#include <zeno/types.hpp>

#include <compare>
#include <optional>
#include <vector>

namespace zeno
{
/// Durations of the flights between central cities: table[i][j] = table[j][i]
/// for the cities i and j (0-based), and 0 on the diagonal.
using FlightTable = std::vector<std::vector<Time>>;

/// A MultiZenoTravel instance: t passengers and p planes start in the initial
/// city C_I and must all end in the goal city C_G; there is no direct flight
/// between C_I and C_G. Central city i is reached from C_I in d[i], from C_G in
/// dbar[i], and every landing in it costs c[i]. Every pair of central cities is
/// joined by a flight, of duration centralFlight(i, j).
///
/// The solver never flies a central flight. Which theorem makes its front exact
/// depends on them (zeno/flights.hpp): (A1), central flights no faster than
/// through a hub, which the default table satisfies, or (AΔ), the triangle
/// inequality (Theorems 4.4 and 4.5 of doc/theory/exact-front.md).
struct Instance
{
    std::vector<Time> d;    ///< durations C_I <-> i
    std::vector<Time> dbar; ///< durations C_G <-> i (equal to d when symmetric)
    std::vector<Cost> c;    ///< landing costs
    int t = 0;              ///< passengers
    int p = 0;              ///< planes
    /// Central flights, or std::nullopt for the default table
    /// max(d_i, dbar_i) + max(d_j, dbar_j) + 100, which satisfies (A1) and
    /// (A1-NS) and violates (AΔ).
    std::optional<FlightTable> central;

    [[nodiscard]] int n() const noexcept { return static_cast<int>(d.size()); }
    /// Minimum number of landings of a plan, 2t - p (counting lemma).
    [[nodiscard]] int landings() const noexcept { return 2 * t - p; }
    [[nodiscard]] bool symmetric() const { return d == dbar; }
    /// Duration of the flight between central cities i != j (0-based): the
    /// table's entry, or the default.
    [[nodiscard]] Time centralFlight(int i, int j) const;

    /// Throws std::invalid_argument unless 1 <= p <= t, n >= 1, the vectors have
    /// length n, every value is non-negative, and a central table, if any, is
    /// n x n, symmetric, with a zero diagonal.
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
