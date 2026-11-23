#include <zeno/one_plane.hpp>

#include <algorithm>
#include <stdexcept>

namespace zeno
{
OnePlaneTable::OnePlaneTable(std::span<const Time> d, std::span<const Cost> c, int maxLandings, Time maxLevel)
    : maxLandings_(maxLandings)
    , width_(static_cast<std::size_t>(maxLevel) + 1)
{
    if(maxLandings < 0 || maxLevel < 0 || d.size() != c.size())
        throw std::invalid_argument("OnePlaneTable: invalid arguments");
    table_.assign(static_cast<std::size_t>(maxLandings + 1) * width_, kInfCost);
    std::fill_n(table_.begin(), width_, Cost{0});

    for(int m = 1; m <= maxLandings; ++m)
    {
        const Cost* prev = table_.data() + static_cast<std::size_t>(m - 1) * width_;
        Cost* cur = table_.data() + static_cast<std::size_t>(m) * width_;
        for(std::size_t i = 0; i < d.size(); ++i)
        {
            const auto shift = static_cast<std::size_t>(d[i]);
            if(shift >= width_)
                continue;
            const Cost ci = c[i];
            // cur[T] = min(cur[T], c_i + prev[T - d_i]); contiguous, vectorisable.
            // prev holds finite values or kInfCost, and kInfCost + c_i stays
            // above kInfCost without overflow, so the result is clamped below.
            for(std::size_t level = shift; level < width_; ++level)
                cur[level] = std::min(cur[level], prev[level - shift] + ci);
        }
        for(std::size_t level = 0; level < width_; ++level)
            cur[level] = std::min(cur[level], kInfCost);
    }
}
} // namespace zeno
