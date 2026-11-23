#pragma once

#include <zeno/forest.hpp>
#include <zeno/instance.hpp>

#include <cstdint>
#include <vector>

namespace zeno
{
struct SolveOptions
{
    unsigned threads = 0; ///< 0: hardware concurrency
};

/// How the value E(T) of a level was established.
enum class LevelSource : std::uint8_t
{
    Unknown,
    Closed,       ///< closed form (cheapest point)
    Bracket,      ///< lower bound L meets the pairs bound U
    Pairs,        ///< U is exact: useful trees have at most 2 planes
    Chains,       ///< L meets U3, or U3 is exact (useful trees have at most 3 planes)
    Exact,        ///< link-forest DP with trees up to maxTree planes
    Monotone,     ///< E non-increasing: equal values at both ends of an interval
};

struct SolveStats
{
    Time lowestLevel = 0, highestLevel = 0; ///< scaled half makespans
    Time scale = 1;                         ///< durations were divided by this
    int reducedCities = 0;
    int maxTree = 0;
    std::uint64_t levels = 0;              ///< levels in [lowest, highest]
    std::uint64_t closedByBracket = 0;     ///< L = U
    std::uint64_t closedByPairs = 0;       ///< U exact (maxTree <= 2)
    std::uint64_t closedByChains = 0;      ///< settled by U3
    std::uint64_t exactCalls = 0;          ///< link-forest DP evaluations
    std::uint64_t closedByMonotonicity = 0;
    LevelStats work;                       ///< summed DP work
    double secondsTable = 0, secondsBracket = 0, secondsChains = 0, secondsExact = 0;
};

struct SolveResult
{
    Front front;
    SolveStats stats;
};

/// Exact Pareto front of a symmetric instance (assumption A1 on central
/// flights, which every generated instance satisfies). Throws
/// std::invalid_argument for invalid or non-symmetric instances.
[[nodiscard]] SolveResult solveFront(const Instance& instance, const SolveOptions& options = {});
} // namespace zeno
