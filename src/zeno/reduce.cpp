#include <zeno/reduce.hpp>

#include <algorithm>
#include <numeric>
#include <stdexcept>
#include <tuple>

namespace zeno
{
namespace
{
Time ceilDiv(Time a, Time b) { return (a + b - 1) / b; }
} // namespace

Time ReducedInstance::lowestLevel() const noexcept
{
    return *std::ranges::min_element(low) * ceilDiv(landings(), p);
}

int ReducedInstance::cheapest() const noexcept
{
    int best = 0;
    for(int i = 1; i < n(); ++i)
    {
        const auto k = static_cast<std::size_t>(i), b = static_cast<std::size_t>(best);
        if(c[k] < c[b] || (c[k] == c[b] && fill[k] < fill[b]))
            best = i;
    }
    return best;
}

Time ReducedInstance::highestLevel() const noexcept
{
    const Time perPlane = ceilDiv(landings(), p);
    const Time weight = fill[static_cast<std::size_t>(cheapest())];
    if(symmetric)
        return weight * perPlane;
    // Odd groups of crossings only: at most ceil(s / p) + 1 landings each.
    return weight * (perPlane + 1);
}

ReducedInstance reduce(const Instance& instance)
{
    instance.validate();
    const std::size_t n = static_cast<std::size_t>(instance.n());
    ReducedInstance r;
    r.t = instance.t;
    r.p = instance.p;
    r.symmetric = instance.symmetric();

    std::vector<int> order(n);
    std::iota(order.begin(), order.end(), 0);
    const auto& d = instance.d;
    const auto& db = instance.dbar;
    const auto& c = instance.c;
    std::ranges::sort(order, [&](int a, int b) {
        const auto ia = static_cast<std::size_t>(a), ib = static_cast<std::size_t>(b);
        return std::tuple(d[ia], db[ia], c[ia], a) < std::tuple(d[ib], db[ib], c[ib], b);
    });
    // Keep a city unless an earlier one (lexicographically smaller) is at
    // least as good in all three coordinates; for symmetric instances this is
    // the staircase by duration.
    std::vector<int> kept;
    for(int i : order)
    {
        const auto k = static_cast<std::size_t>(i);
        const bool dominated = std::ranges::any_of(kept, [&](int j) {
            const auto m = static_cast<std::size_t>(j);
            return d[m] <= d[k] && db[m] <= db[k] && c[m] <= c[k];
        });
        if(!dominated)
            kept.push_back(i);
    }
    for(int i : kept)
    {
        const auto k = static_cast<std::size_t>(i);
        r.d.push_back(d[k]);
        r.dbar.push_back(db[k]);
        r.c.push_back(c[k]);
        r.original.push_back(i);
    }

    Time g = 0;
    for(Time v : r.d)
        g = std::gcd(g, v);
    for(Time v : r.dbar)
        g = std::gcd(g, v);
    r.scale = g == 0 ? 1 : g;
    for(Time& v : r.d)
        v /= r.scale;
    for(Time& v : r.dbar)
        v /= r.scale;

    const std::size_t m = r.d.size();
    if(r.symmetric)
    {
        r.fill = r.drop = r.pick = r.low = r.d;
        r.makespanPerLevel = 2 * r.scale;
    }
    else
    {
        for(std::size_t i = 0; i < m; ++i)
        {
            r.fill.push_back(r.d[i] + r.dbar[i]);
            r.drop.push_back(2 * r.d[i]);
            r.pick.push_back(2 * r.dbar[i]);
            r.low.push_back(2 * std::min(r.d[i], r.dbar[i]));
        }
        r.makespanPerLevel = r.scale;
    }
    const auto sortedBy = [&](const std::vector<Time>& w) {
        std::vector<int> idx(m);
        std::iota(idx.begin(), idx.end(), 0);
        std::ranges::stable_sort(idx, [&](int a, int b) { return w[static_cast<std::size_t>(a)] < w[static_cast<std::size_t>(b)]; });
        return idx;
    };
    r.byDrop = sortedBy(r.drop);
    r.byPick = sortedBy(r.pick);
    return r;
}
} // namespace zeno
