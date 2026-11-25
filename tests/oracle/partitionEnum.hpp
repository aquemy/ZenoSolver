////////////////////////////////////////////////////////////
/// \file partitionEnum.hpp
/// \brief Enumeration oracle for symmetric instances.
///
/// Enumerates every landing multiset X of size s = 2t - p and computes
/// M(X), the smallest makespan of an admissible partition of X into p
/// groups (each connected component of the planes x cities graph holds an
/// even number of planes with an even number of landings), by exhaustive
/// branch and bound. The front is the Pareto set of (cost(X), M(X)).
///
/// This is the characterisation of Theorem 4.5 of
/// doc/theory/exact-front.md, computed without any of the solver's
/// dynamic programs. It shares no code with the library.
////////////////////////////////////////////////////////////
#pragma once

#include <algorithm>
#include <cstdint>
#include <functional>
#include <limits>
#include <map>
#include <numeric>
#include <utility>
#include <vector>

namespace oracle::partition
{
using Int = std::int64_t;
inline constexpr Int kInf = std::numeric_limits<Int>::max() / 4;

struct Instance
{
    std::vector<Int> d, c;
    int t = 0, p = 0;
    int n() const { return static_cast<int>(d.size()); }
    int s() const { return 2 * t - p; }
};

/// Smallest makespan (2 * max group duration) of an admissible partition of
/// the multiset x (x[i] landings in city i) into p non-empty groups.
class PartitionSearch
{
public:
    PartitionSearch(const Instance& in, const std::vector<int>& x)
        : in_(in)
        , count_(static_cast<std::size_t>(in.p), std::vector<int>(static_cast<std::size_t>(in.n()), 0))
        , load_(static_cast<std::size_t>(in.p), 0)
        , size_(static_cast<std::size_t>(in.p), 0)
    {
        for(int i = 0; i < in.n(); ++i)
            for(int k = 0; k < x[static_cast<std::size_t>(i)]; ++k)
                jobs_.push_back(i);
        std::sort(jobs_.begin(), jobs_.end(), [&](int a, int b) {
            return in.d[static_cast<std::size_t>(a)] != in.d[static_cast<std::size_t>(b)] ? in.d[static_cast<std::size_t>(a)] > in.d[static_cast<std::size_t>(b)] : a < b;
        });
        assigned_.assign(jobs_.size(), 0);
        Int sum = 0, longest = 0;
        for(int j : jobs_)
        {
            sum += in.d[static_cast<std::size_t>(j)];
            longest = std::max(longest, in.d[static_cast<std::size_t>(j)]);
        }
        bound_ = 2 * std::max<Int>((sum + in.p - 1) / in.p, longest);
    }

    Int run()
    {
        rec(0, 0);
        return best_;
    }

private:
    bool admissible() const
    {
        const int p = in_.p, n = in_.n();
        std::vector<int> parent(static_cast<std::size_t>(p + n));
        std::iota(parent.begin(), parent.end(), 0);
        std::function<int(int)> find = [&](int v) {
            return parent[static_cast<std::size_t>(v)] == v ? v : parent[static_cast<std::size_t>(v)] = find(parent[static_cast<std::size_t>(v)]);
        };
        for(int k = 0; k < p; ++k)
            for(int i = 0; i < n; ++i)
                if(count_[static_cast<std::size_t>(k)][static_cast<std::size_t>(i)] > 0)
                    parent[static_cast<std::size_t>(find(k))] = find(p + i);
        std::vector<int> even(static_cast<std::size_t>(p + n), 0);
        for(int k = 0; k < p; ++k)
            if(size_[static_cast<std::size_t>(k)] % 2 == 0)
                ++even[static_cast<std::size_t>(find(k))];
        return std::all_of(even.begin(), even.end(), [](int v) { return v % 2 == 0; });
    }

    void rec(std::size_t j, int used)
    {
        if(best_ == bound_)
            return;
        if(j == jobs_.size())
        {
            if(used == in_.p && admissible())
                best_ = std::min(best_, 2 * *std::max_element(load_.begin(), load_.end()));
            return;
        }
        if(static_cast<int>(jobs_.size() - j) < in_.p - used)
            return;
        // Planes are interchangeable (numbered by first use), and so are equal
        // landings (assigned to non-decreasing plane numbers).
        const int from = (j > 0 && jobs_[j] == jobs_[j - 1]) ? assigned_[j - 1] : 0;
        const Int w = in_.d[static_cast<std::size_t>(jobs_[j])];
        for(int k = from; k < std::min(used + 1, in_.p); ++k)
        {
            const auto kk = static_cast<std::size_t>(k);
            if(2 * (load_[kk] + w) >= best_)
                continue;
            load_[kk] += w;
            ++size_[kk];
            ++count_[kk][static_cast<std::size_t>(jobs_[j])];
            assigned_[j] = k;
            rec(j + 1, std::max(used, k + 1));
            load_[kk] -= w;
            --size_[kk];
            --count_[kk][static_cast<std::size_t>(jobs_[j])];
            if(best_ == bound_)
                return;
        }
    }

    const Instance& in_;
    std::vector<int> jobs_, assigned_;
    std::vector<std::vector<int>> count_;
    std::vector<Int> load_;
    std::vector<int> size_;
    Int best_ = kInf, bound_ = 0;
};

/// (cost(X), M(X)) for every landing multiset X of size s.
inline std::vector<std::pair<Int, Int>> allMultisets(const Instance& in)
{
    std::vector<std::pair<Int, Int>> out;
    std::vector<int> x(static_cast<std::size_t>(in.n()), 0);
    std::function<void(int, int)> rec = [&](int i, int left) {
        if(i == in.n() - 1)
        {
            x[static_cast<std::size_t>(i)] = left;
            Int cost = 0;
            for(int k = 0; k < in.n(); ++k)
                cost += x[static_cast<std::size_t>(k)] * in.c[static_cast<std::size_t>(k)];
            PartitionSearch search(in, x);
            const Int m = search.run();
            if(m < kInf)
                out.emplace_back(cost, m);
            return;
        }
        for(int v = left; v >= 0; --v)
        {
            x[static_cast<std::size_t>(i)] = v;
            rec(i + 1, left - v);
        }
        x[static_cast<std::size_t>(i)] = 0;
    };
    rec(0, in.s());
    return out;
}

/// The exact front as (cost, makespan) pairs by increasing cost.
inline std::vector<std::pair<Int, Int>> paretoFront(const Instance& in)
{
    std::map<Int, Int> bestPerCost;
    for(auto [cost, makespan] : allMultisets(in))
    {
        auto it = bestPerCost.find(cost);
        if(it == bestPerCost.end() || makespan < it->second)
            bestPerCost[cost] = makespan;
    }
    std::vector<std::pair<Int, Int>> front;
    for(auto [cost, makespan] : bestPerCost)
        if(front.empty() || makespan < front.back().second)
            front.emplace_back(cost, makespan);
    return front;
}

/// E(T) = cheapest cost with M(X) <= 2T, for T = 0..maxLevel.
inline std::vector<Int> levelValues(const Instance& in, Int maxLevel)
{
    std::vector<Int> e(static_cast<std::size_t>(maxLevel + 1), kInf);
    for(auto [cost, makespan] : allMultisets(in))
        for(Int T = (makespan + 1) / 2; T <= maxLevel; ++T)
            e[static_cast<std::size_t>(T)] = std::min(e[static_cast<std::size_t>(T)], cost);
    return e;
}
} // namespace oracle::partition
