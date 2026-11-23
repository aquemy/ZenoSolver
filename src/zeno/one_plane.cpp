#include <zeno/one_plane.hpp>

#include <algorithm>
#include <stdexcept>

namespace zeno
{
OnePlaneTable::OnePlaneTable(std::span<const Time> d, std::span<const Cost> c, int maxLandings, Time maxLevel, Layout layout)
    : d_(d.begin(), d.end())
    , c_(c.begin(), c.end())
    , maxLandings_(maxLandings)
    , maxLevel_(maxLevel)
    , dense_(false)
    , width_(static_cast<std::size_t>(maxLevel) + 1)
{
    if(maxLandings < 0 || maxLevel < 0 || d.size() != c.size())
        throw std::invalid_argument("OnePlaneTable: invalid arguments");
    const auto cells = static_cast<std::size_t>(maxLandings + 1) * width_;
    dense_ = layout == Layout::Dense || (layout == Layout::Automatic && cells <= kDenseCells);
    if(dense_)
        buildDense();
    else
        buildStaircase();
}

void OnePlaneTable::buildDense()
{
    table_.assign(static_cast<std::size_t>(maxLandings_ + 1) * width_, kInfCost);
    std::fill_n(table_.begin(), width_, Cost{0});
    for(int m = 1; m <= maxLandings_; ++m)
    {
        const Cost* prev = table_.data() + static_cast<std::size_t>(m - 1) * width_;
        Cost* cur = table_.data() + static_cast<std::size_t>(m) * width_;
        for(std::size_t i = 0; i < d_.size(); ++i)
        {
            const auto shift = static_cast<std::size_t>(d_[i]);
            if(shift >= width_)
                continue;
            const Cost ci = c_[i];
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

void OnePlaneTable::buildStaircase()
{
    stairs_.assign(static_cast<std::size_t>(maxLandings_ + 1), {});
    stairs_[0].push_back({0, 0, -1, -1});
    std::vector<Stair> candidates;
    for(int m = 1; m <= maxLandings_; ++m)
    {
        const auto& prev = stairs_[static_cast<std::size_t>(m - 1)];
        candidates.clear();
        for(std::size_t i = 0; i < d_.size(); ++i)
            for(std::size_t k = 0; k < prev.size(); ++k)
            {
                const Time load = prev[k].load + d_[i];
                if(load > maxLevel_)
                    break; // prev is sorted by load
                candidates.push_back({load, prev[k].cost + c_[i], static_cast<int>(i), static_cast<int>(k)});
            }
        std::ranges::sort(candidates, [](const Stair& a, const Stair& b) { return a.load != b.load ? a.load < b.load : a.cost < b.cost; });
        auto& out = stairs_[static_cast<std::size_t>(m)];
        for(const Stair& s : candidates)
            if(out.empty() || s.cost < out.back().cost)
            {
                if(!out.empty() && out.back().load == s.load)
                    continue; // same load, higher cost (sorted)
                out.push_back(s);
            }
    }
}

int OnePlaneTable::stairIndex(int m, Time level) const noexcept
{
    // The last point with load <= level holds the cheapest cost within it.
    const auto& steps = stairs_[static_cast<std::size_t>(m)];
    const auto it = std::upper_bound(steps.begin(), steps.end(), level, [](Time v, const Stair& s) { return v < s.load; });
    return static_cast<int>(it - steps.begin()) - 1;
}

Cost OnePlaneTable::stairLookup(int m, Time level) const noexcept
{
    const int i = stairIndex(m, level);
    return i < 0 ? kInfCost : stairs_[static_cast<std::size_t>(m)][static_cast<std::size_t>(i)].cost;
}

std::size_t OnePlaneTable::size() const noexcept
{
    if(dense_)
        return table_.size();
    std::size_t total = 0;
    for(const auto& s : stairs_)
        total += s.size();
    return total;
}

std::vector<int> OnePlaneTable::witness(int m, Time level) const
{
    if(m < 0 || m > maxLandings_ || level < 0 || level > maxLevel() || isInf((*this)(m, level)))
        throw std::invalid_argument("OnePlaneTable::witness: no multiset realises this entry");
    std::vector<int> cities;
    if(!dense_)
    {
        for(int i = stairIndex(m, level); m > 0; --m)
        {
            const Stair& s = stairs_[static_cast<std::size_t>(m)][static_cast<std::size_t>(i)];
            cities.push_back(s.city);
            i = s.previous;
        }
        return cities;
    }
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
