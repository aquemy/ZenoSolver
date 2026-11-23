#pragma once

#include <cstdint>
#include <limits>

namespace zeno
{
/// Costs and durations are integers. Durations are in the instance's time unit;
/// the solver works with half-makespans T, so a plan's makespan is 2 * T.
using Cost = std::int64_t;
using Time = std::int64_t;

/// "No solution". Large enough to dominate any reachable cost, small enough
/// that adding two of them does not overflow.
inline constexpr Cost kInfCost = std::numeric_limits<Cost>::max() / 4;

[[nodiscard]] constexpr bool isInf(Cost value) noexcept
{
    return value >= kInfCost;
}

/// Saturating addition: infinity absorbs.
[[nodiscard]] constexpr Cost addCost(Cost a, Cost b) noexcept
{
    return (isInf(a) || isInf(b)) ? kInfCost : a + b;
}
} // namespace zeno
