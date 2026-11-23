#include <zeno/one_plane.hpp>

#include <algorithm>
#include <stdexcept>

namespace zeno
{
OnePlaneTable::OnePlaneTable(std::span<const Time> d, std::span<const Cost> c, int maxLandings, Time maxLevel)
    : d_(d.begin(), d.end())
    , c_(c.begin(), c.end())
    , maxLandings_(maxLandings)
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
std::vector<int> OnePlaneTable::witness(int m, Time level) const
{
    if(m < 0 || m > maxLandings_ || level < 0 || level > maxLevel() || isInf((*this)(m, level)))
        throw std::invalid_argument("OnePlaneTable::witness: no multiset realises this entry");
    std::vector<int> cities;
    for(; m > 0; --m)
    {
        const Cost target = (*this)(m, level);
        std::size_t i = 0;
        while(i < d_.size() && (d_[i] > level || (*this)(m - 1, level - d_[i]) + c_[i] != target))
            ++i;
        if(i == d_.size())
            throw std::logic_error("OnePlaneTable::witness: inconsistent table");
        cities.push_back(static_cast<int>(i));
        level -= d_[i];
    }
    return cities;
}
} // namespace zeno
