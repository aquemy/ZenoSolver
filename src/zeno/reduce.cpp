#include <zeno/reduce.hpp>

#include <algorithm>
#include <numeric>
#include <stdexcept>

namespace zeno
{
namespace
{
Time ceilDiv(Time a, Time b) { return (a + b - 1) / b; }
} // namespace

Time ReducedInstance::lowestLevel() const noexcept
{
    return d.front() * ceilDiv(landings(), p);
}

Time ReducedInstance::highestLevel() const noexcept
{
    return d.back() * ceilDiv(landings(), p);
}

ReducedInstance reduce(const Instance& instance)
{
    instance.validate();
    if(!instance.symmetric())
        throw std::invalid_argument("reduce: the instance is not symmetric");

    std::vector<int> order(static_cast<std::size_t>(instance.n()));
    std::iota(order.begin(), order.end(), 0);
    std::ranges::sort(order, [&](int a, int b) {
        const auto ia = static_cast<std::size_t>(a), ib = static_cast<std::size_t>(b);
        return instance.d[ia] != instance.d[ib] ? instance.d[ia] < instance.d[ib]
             : instance.c[ia] != instance.c[ib] ? instance.c[ia] < instance.c[ib]
                                                : a < b;
    });

    // Staircase: by increasing duration, keep a city only if it is strictly
    // cheaper than every faster-or-equal city kept so far.
    ReducedInstance r;
    r.t = instance.t;
    r.p = instance.p;
    for(int i : order)
    {
        const auto k = static_cast<std::size_t>(i);
        if(!r.c.empty() && instance.c[k] >= r.c.back())
            continue;
        r.d.push_back(instance.d[k]);
        r.c.push_back(instance.c[k]);
        r.original.push_back(i);
    }

    Time g = 0;
    for(Time v : r.d)
        g = std::gcd(g, v);
    if(g > 1)
        for(Time& v : r.d)
            v /= g;
    r.scale = g == 0 ? 1 : g;
    return r;
}
} // namespace zeno
