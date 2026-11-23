#pragma once

#include <zeno/parallel.hpp>
#include <zeno/types.hpp>

#include <algorithm>
#include <stdexcept>
#include <string>
#include <utility>
#include <vector>

namespace zeno
{
/// Breakpoints of a non-increasing function f on the levels [lo, hi], given
/// f(lo) and f(hi): the pairs (lo, f(lo)) and (T, f(T)) for every T in
/// (lo, hi] with f(T) < f(T - 1), by increasing T.
///
/// Every open interval (a, b) with f(a) > f(b) is split at up to `threads`
/// evenly spaced levels, evaluated in parallel (f must be thread-safe);
/// pieces with equal ends are constant, and a piece (a, a + 1) has its
/// breakpoint at a + 1. With r breakpoints this evaluates O(r log(hi - lo))
/// levels. Throws std::logic_error if f is seen to increase.
template<class F>
std::vector<std::pair<Time, Cost>> breakpoints(Time lo, Cost flo, Time hi, Cost fhi, F&& f, unsigned threads)
{
    struct Interval
    {
        Time a, b;
        Cost fa, fb;
    };
    std::vector<std::pair<Time, Cost>> points{{lo, flo}};
    if(fhi > flo)
        throw std::logic_error("breakpoints: f increases between the ends");
    std::vector<Interval> open;
    if(flo > fhi)
        open.push_back({lo, hi, flo, fhi});
    const unsigned workers = workerCount(threads);
    while(!open.empty())
    {
        std::vector<Time> probes;
        std::vector<std::size_t> first;
        for(const Interval& iv : open)
        {
            first.push_back(probes.size());
            if(iv.b == iv.a + 1)
                continue;
            const Time k = std::clamp<Time>(static_cast<Time>(workers) / static_cast<Time>(open.size()), 1, iv.b - iv.a - 1);
            for(Time j = 1; j <= k; ++j)
                probes.push_back(iv.a + j * (iv.b - iv.a) / (k + 1));
        }
        first.push_back(probes.size());
        std::vector<Cost> values(probes.size());
        parallelFor(probes.size(), threads, [&](std::size_t i) { values[i] = f(probes[i]); });

        std::vector<Interval> next;
        for(std::size_t k = 0; k < open.size(); ++k)
        {
            const Interval& iv = open[k];
            if(iv.b == iv.a + 1)
            {
                points.emplace_back(iv.b, iv.fb);
                continue;
            }
            Time a = iv.a;
            Cost fa = iv.fa;
            for(std::size_t i = first[k]; i <= first[k + 1]; ++i)
            {
                const bool end = i == first[k + 1];
                const Time b = end ? iv.b : probes[i];
                const Cost fb = end ? iv.fb : values[i];
                if(fb > fa)
                    throw std::logic_error("breakpoints: f increases at level " + std::to_string(b));
                if(fb < fa)
                    next.push_back({a, b, fa, fb});
                a = b;
                fa = fb;
            }
        }
        open = std::move(next);
    }
    std::ranges::sort(points);
    return points;
}
} // namespace zeno
