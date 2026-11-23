#pragma once

#include <zeno/types.hpp>

#include <span>
#include <vector>

namespace zeno
{
/// G[m][T]: minimum cost of a multiset of m landings whose durations sum to at
/// most T (+infinity when none exists), for 0 <= m <= maxLandings and
/// 0 <= T <= maxLevel. G[0][T] = 0 and G[m][T] = min_i c_i + G[m-1][T - d_i].
/// G is non-increasing in T. Building it takes O(n * maxLandings * maxLevel).
class OnePlaneTable
{
public:
    OnePlaneTable(std::span<const Time> d, std::span<const Cost> c, int maxLandings, Time maxLevel);

    /// G[m][T]; infinity for T < 0. Requires 0 <= m <= maxLandings() and T <= maxLevel().
    [[nodiscard]] Cost operator()(int m, Time level) const noexcept
    {
        if(level < 0)
            return kInfCost;
        return table_[static_cast<std::size_t>(m) * width_ + static_cast<std::size_t>(level)];
    }

    /// Row m: G[m][0..maxLevel].
    [[nodiscard]] std::span<const Cost> row(int m) const noexcept
    {
        return {table_.data() + static_cast<std::size_t>(m) * width_, width_};
    }

    [[nodiscard]] int maxLandings() const noexcept { return maxLandings_; }
    [[nodiscard]] Time maxLevel() const noexcept { return static_cast<Time>(width_) - 1; }

private:
    int maxLandings_;
    std::size_t width_;
    std::vector<Cost> table_;
};
} // namespace zeno
