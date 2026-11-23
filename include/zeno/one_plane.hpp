#pragma once

#include <zeno/types.hpp>

#include <span>
#include <vector>

namespace zeno
{
/// G[m][T]: minimum cost of a multiset of m landings whose durations sum to at
/// most T (+infinity when none exists), for 0 <= m <= maxLandings and
/// 0 <= T <= maxLevel. G[0][T] = 0 and G[m][T] = min_i c_i + G[m-1][T - d_i].
/// G is non-increasing in T.
///
/// Two representations, chosen by size:
/// - dense, one row of maxLevel + 1 entries per m: O(n * maxLandings *
///   maxLevel) to build, O(1) lookups;
/// - staircase, per m the Pareto set of (load, cost) of m-multisets (load
///   increasing, cost decreasing): memory and time independent of the
///   magnitude of the durations, O(log) lookups.
class OnePlaneTable
{
public:
    enum class Layout
    {
        Automatic, ///< dense unless it would exceed kDenseCells cells
        Dense,
        Staircase,
    };
    static constexpr std::size_t kDenseCells = std::size_t{1} << 22;

    OnePlaneTable(std::span<const Time> d, std::span<const Cost> c, int maxLandings, Time maxLevel, Layout layout = Layout::Automatic);

    /// G[m][T]; infinity for T < 0. Requires 0 <= m <= maxLandings() and T <= maxLevel().
    [[nodiscard]] Cost operator()(int m, Time level) const noexcept
    {
        if(level < 0)
            return kInfCost;
        if(dense_)
            return table_[static_cast<std::size_t>(m) * width_ + static_cast<std::size_t>(level)];
        return stairLookup(m, level);
    }

    [[nodiscard]] int maxLandings() const noexcept { return maxLandings_; }
    [[nodiscard]] Time maxLevel() const noexcept { return maxLevel_; }
    [[nodiscard]] bool dense() const noexcept { return dense_; }
    /// Entries stored (cells, or staircase points).
    [[nodiscard]] std::size_t size() const noexcept;

    /// A multiset realising G[m][T], as m city indices. Requires a finite value.
    [[nodiscard]] std::vector<int> witness(int m, Time level) const;

private:
    struct Stair
    {
        Time load = 0;
        Cost cost = 0;
        int city = -1;     ///< last city added
        int previous = -1; ///< index in the staircase of m - 1
    };

    [[nodiscard]] Cost stairLookup(int m, Time level) const noexcept;
    [[nodiscard]] int stairIndex(int m, Time level) const noexcept;
    void buildDense();
    void buildStaircase();

    std::vector<Time> d_;
    std::vector<Cost> c_;
    int maxLandings_;
    Time maxLevel_;
    bool dense_;
    std::size_t width_;
    std::vector<Cost> table_;
    std::vector<std::vector<Stair>> stairs_;
};
} // namespace zeno
