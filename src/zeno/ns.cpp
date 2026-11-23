#include <zeno/ns.hpp>

#include <zeno/breakpoints.hpp>
#include <zeno/forest.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/parallel.hpp>
#include <zeno/reduce.hpp>

#include <algorithm>
#include <array>
#include <chrono>
#include <iterator>
#include <mutex>
#include <stdexcept>
#include <string>

namespace zeno
{
namespace
{
std::size_t at(int v) { return static_cast<std::size_t>(v); }

/// Per-plane table of the role relaxation: the cheapest m landings with load
/// <= T of which an odd number are crossings (weight fill) and the others
/// drop-offs or pick-ups (weight low = min(drop, pick)). Staircases per (m,
/// parity of the crossings).
class OddCrossingTable
{
public:
    OddCrossingTable(const ReducedInstance& r, int maxLandings, Time maxLevel)
        : stairs_(at(maxLandings + 1))
    {
        stairs_[0][0].push_back({0, 0});
        std::vector<Stair> candidates;
        for(int m = 1; m <= maxLandings; ++m)
            for(int parity = 0; parity < 2; ++parity)
            {
                candidates.clear();
                const auto extend = [&](const std::vector<Stair>& from, const std::vector<Time>& weight) {
                    for(int i = 0; i < r.n(); ++i)
                        for(const Stair& s : from)
                        {
                            const Time load = s.load + weight[at(i)];
                            if(load > maxLevel)
                                break;
                            candidates.push_back({load, s.cost + r.c[at(i)]});
                        }
                };
                extend(stairs_[at(m - 1)][at(1 - parity)], r.fill); // one more crossing
                extend(stairs_[at(m - 1)][at(parity)], r.low);      // one more drop-off or pick-up
                std::ranges::sort(candidates, [](const Stair& a, const Stair& b) { return a.load != b.load ? a.load < b.load : a.cost < b.cost; });
                auto& out = stairs_[at(m)][at(parity)];
                for(const Stair& s : candidates)
                    if((out.empty() || s.cost < out.back().cost) && (out.empty() || out.back().load != s.load))
                        out.push_back(s);
            }
    }

    Cost odd(int m, Time level) const
    {
        const auto& steps = stairs_[at(m)][1];
        const auto it = std::upper_bound(steps.begin(), steps.end(), level, [](Time v, const Stair& s) { return v < s.load; });
        return it == steps.begin() ? kInfCost : std::prev(it)->cost;
    }

private:
    struct Stair
    {
        Time load = 0;
        Cost cost = 0;
    };
    std::vector<std::array<std::vector<Stair>, 2>> stairs_;
};

/// Cheapest way to give p planes s landings, plane k taking m_k >= 1 at
/// cost group(m_k).
template<class Group>
Cost overPlanes(int p, int s, Group group)
{
    std::vector<Cost> best(at(s + 1), kInfCost), next;
    best[0] = 0;
    for(int k = 0; k < p; ++k)
    {
        next.assign(at(s + 1), kInfCost);
        for(int j = 0; j < s; ++j)
        {
            if(isInf(best[at(j)]))
                continue;
            for(int m = 1; j + m <= s; ++m)
            {
                const Cost g = group(m);
                if(!isInf(g))
                    next[at(j + m)] = std::min(next[at(j + m)], best[at(j)] + g);
            }
        }
        best.swap(next);
    }
    return best[at(s)];
}

/// Smallest level in [lo, hi] at which the non-increasing f is finite (f(hi) finite).
template<class F>
Time firstFinite(Time lo, Time hi, F f)
{
    while(lo < hi)
    {
        const Time mid = lo + (hi - lo) / 2;
        if(isInf(f(mid)))
            lo = mid + 1;
        else
            hi = mid;
    }
    return lo;
}
} // namespace

bool BracketResult::exact() const
{
    return !upper.empty() && fastestLower == upper.front().makespan &&
           std::ranges::none_of(gapProof, [](GapProof g) { return g == GapProof::Open; });
}

std::vector<std::string> BracketResult::assumptions() const
{
    if(fastestProof == GapProof::Roles || std::ranges::any_of(gapProof, [](GapProof g) { return g == GapProof::Roles; }))
        return {"A1-NS"};
    return {};
}

BracketResult solveBracket(const Instance& instance, const SolveOptions& options)
{
    instance.validate();
    const auto start = std::chrono::steady_clock::now();
    const unsigned threads = workerCount(options.threads);
    // Two orientations of a link forest: every plane picks up at most once
    // (the instance itself), or drops off at most once (the time reversal of
    // the mirrored instance).
    const Instance mirror = mirrored(instance);
    const ReducedInstance r = reduce(instance);
    const ReducedInstance rm = reduce(mirror);
    const Time lo = r.lowestLevel(), hi = r.highestLevel();
    const OnePlaneTable G(r.fill, r.c, r.maxGroup(), hi, options.table);
    const OnePlaneTable Gm(rm.fill, rm.c, rm.maxGroup(), hi, options.table);
    const int Q = r.maxTree();

    BracketResult result;
    auto& stats = result.stats;
    stats.lowestLevel = lo;
    stats.highestLevel = hi;
    stats.scale = r.scale;
    stats.reducedCities = r.n();
    stats.maxTree = Q;
    stats.levels = static_cast<std::uint64_t>(hi - lo + 1);

    std::mutex mutex;
    const auto upperAt = [&](Time T) {
        LevelStats work;
        const Cost u = std::min(forestCost(r, G, T, Q, &work), forestCost(rm, Gm, T, Q, &work));
        const std::scoped_lock lock(mutex);
        ++stats.exactCalls;
        stats.work.states += work.states;
        stats.work.relaxations += work.relaxations;
        return u;
    };

    // 1. Breakpoints of the forest bound, then a simulated plan for each.
    const Time first = firstFinite(lo, hi, upperAt);
    const auto points = breakpoints(first, upperAt(first), hi, upperAt(hi), upperAt, threads);
    std::vector<FrontPoint> achieved(points.size());
    std::vector<Plan> plans(points.size());
    parallelFor(points.size(), threads, [&](std::size_t i) {
        const auto [T, cost] = points[i];
        const ForestProgram direct(r, G, T, Q);
        Plan plan;
        if(direct.value() == cost)
            plan = buildPlan(instance, r, direct.reconstruct());
        else
        {
            const ForestProgram reversed(rm, Gm, T, Q);
            if(reversed.value() != cost)
                throw std::logic_error("solveBracket: no orientation realises a breakpoint");
            plan = mirrorPlan(buildPlan(mirror, rm, reversed.reconstruct()), instance.n());
        }
        const PlanCheck check = checkPlan(instance, plan);
        if(!check.ok || check.cost != cost)
            throw std::logic_error("solveBracket: a forest plan fails its check: " + (check.ok ? std::string("cost") : check.error));
        achieved[i] = {check.cost, check.makespan};
        plans[i] = std::move(plan);
    });
    // Waiting can delay a plan past its level, so filter the simulated points.
    result.upper = paretoFilter(achieved);
    if(options.plans)
        for(const FrontPoint& point : result.upper)
            for(std::size_t i = 0; i < achieved.size(); ++i)
                if(achieved[i] == point)
                {
                    result.plans.push_back(plans[i]);
                    break;
                }

    // 2. Lower bounds, on tables covering every gap level.
    //  - lemma R: per-plane groups with weights min(drop, pick); no assumption.
    //  - roles (Theorem 6.1, A1-NS): every plan is weakly dominated by a role
    //    configuration, in which each plane flies an odd number >= 1 of
    //    crossings (weight fill) and its other landings weigh at least
    //    min(drop, pick); and, as drop-offs and pick-ups pair up city by
    //    city, the loads of all planes add up to fill(X), so the largest is
    //    at least fill(X) / p.
    const Time maxLevel = std::max(hi, (result.upper.back().makespan - 1) / r.makespanPerLevel);
    const OnePlaneTable Glow(r.low, r.c, r.maxGroup(), maxLevel, options.table);
    const OddCrossingTable roles(r, r.maxGroup(), maxLevel);
    const OnePlaneTable Gtotal(r.fill, r.c, r.landings(), static_cast<Time>(r.p) * maxLevel, OnePlaneTable::Layout::Staircase);
    const auto relaxedAt = [&](Time T) { return T < 0 ? kInfCost : relaxedCost(r, Glow, T); };
    const auto rolesAt = [&](Time T) {
        if(T < 0)
            return kInfCost;
        const Cost perPlane = overPlanes(r.p, r.landings(), [&](int m) { return m <= r.maxGroup() ? roles.odd(m, T) : kInfCost; });
        return std::max(perPlane, Gtotal(r.landings(), static_cast<Time>(r.p) * T));
    };
    const Time fastestRelaxed = firstFinite(0, maxLevel, relaxedAt);
    const Time fastestRoles = firstFinite(fastestRelaxed, maxLevel, rolesAt);
    result.fastestLower = r.makespanPerLevel * fastestRelaxed;
    if(r.makespanPerLevel * fastestRoles > result.fastestLower)
    {
        result.fastestLower = r.makespanPerLevel * fastestRoles;
        result.fastestProof = GapProof::Roles;
    }
    const std::size_t gaps = result.upper.size() - 1;
    result.gapLower.assign(gaps, 0);
    result.gapProof.assign(gaps, GapProof::Open);
    parallelFor(gaps, threads, [&](std::size_t i) {
        const Time level = (result.upper[i + 1].makespan - 1) / r.makespanPerLevel;
        const Cost relaxed = relaxedAt(level);
        const Cost byRoles = rolesAt(level);
        result.gapLower[i] = std::max(relaxed, byRoles);
        if(relaxed >= result.upper[i].cost)
            result.gapProof[i] = GapProof::Relaxed;
        else if(byRoles >= result.upper[i].cost)
            result.gapProof[i] = GapProof::Roles;
    });
    stats.secondsExact = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    return result;
}
} // namespace zeno
