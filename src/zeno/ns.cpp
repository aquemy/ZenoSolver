#include <zeno/ns.hpp>

#include <zeno/breakpoints.hpp>
#include <zeno/forest.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/parallel.hpp>
#include <zeno/reduce.hpp>
#include <zeno/ns_search.hpp>
#include <zeno/roles.hpp>

#include <algorithm>
#include <array>
#include <chrono>
#include <iterator>
#include <limits>
#include <map>
#include <optional>
#include <set>
#include <mutex>
#include <stdexcept>
#include <string>

namespace zeno
{
namespace
{
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
    const auto needsA1 = [](GapProof g) { return g != GapProof::Open && g != GapProof::Relaxed; };
    std::vector<std::string> out;
    if(needsA1(fastestProof) || std::ranges::any_of(gapProof, needsA1))
        out.push_back("A1-NS");
    // A search proof covers event-ordered plans (all PDDL plans), and every
    // plan unless some city has d = dbar = 0 (Theorem 6.9).
    const auto search = [](GapProof g) { return g == GapProof::Search; };
    if(zeroDurationCity && (search(fastestProof) || std::ranges::any_of(gapProof, search)))
        out.push_back("EO");
    return out;
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
    for(int i = 0; i < instance.n(); ++i)
        result.zeroDurationCity = result.zeroDurationCity || (instance.d[static_cast<std::size_t>(i)] == 0 && instance.dbar[static_cast<std::size_t>(i)] == 0);
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
    // Achieved points and their plans; the upper front is their Pareto set
    // (waiting can delay a plan past its level, so filter the simulated points).
    std::vector<std::pair<FrontPoint, Plan>> candidates;
    for(std::size_t i = 0; i < achieved.size(); ++i)
        candidates.emplace_back(achieved[i], std::move(plans[i]));
    const auto rebuildUpper = [&] {
        std::vector<FrontPoint> pts;
        for(const auto& c : candidates)
            pts.push_back(c.first);
        result.upper = paretoFilter(pts);
    };
    rebuildUpper();

    // 2. Lower bounds, on tables covering every gap level.
    //  - lemma R: per-plane groups with weights min(drop, pick); no assumption.
    //  - roles (Theorem 6.1, A1-NS): every plan is weakly dominated by a role
    //    configuration, in which each plane flies an odd number >= 1 of
    //    crossings (weight fill) and its other landings weigh at least
    //    min(drop, pick); and, as drop-offs and pick-ups pair up city by
    //    city, the loads of all planes add up to fill(X), so the largest is
    //    at least fill(X) / p.
    //  - balanced (Theorem 6.1, A1-NS): the cheapest balanced role
    //    configuration itself (BalancedRoles), on the gaps the others leave open.
    const Time maxLevel = std::max(hi, (result.upper.back().makespan - 1) / r.makespanPerLevel);
    const OnePlaneTable Glow(r.low, r.c, r.maxGroup(), maxLevel, options.table);
    const OnePlaneTable Gfill(r.fill, r.c, r.maxGroup(), maxLevel, options.table);
    const RoleRelaxation roles(r, maxLevel);
    const auto relaxedAt = [&](Time T) { return T < 0 ? kInfCost : relaxedCost(r, Glow, T); };
    const auto rolesAt = [&](Time T) { return roles.bound(T); };
    const Time fastestRelaxed = firstFinite(0, maxLevel, relaxedAt);
    const Time fastestRoles = firstFinite(fastestRelaxed, maxLevel, rolesAt);
    result.fastestLower = r.makespanPerLevel * fastestRelaxed;
    if(r.makespanPerLevel * fastestRoles > result.fastestLower)
    {
        result.fastestLower = r.makespanPerLevel * fastestRoles;
        result.fastestProof = GapProof::Roles;
    }
    const auto gapLevel = [&](std::size_t i) { return (result.upper[i + 1].makespan - 1) / r.makespanPerLevel; };
    const auto boundGaps = [&] {
        const std::size_t gaps = result.upper.size() - 1;
        result.gapLower.assign(gaps, 0);
        result.gapProof.assign(gaps, GapProof::Open);
        result.gapMultipliers.assign(gaps, {});
        parallelFor(gaps, threads, [&](std::size_t i) {
            const Cost relaxed = relaxedAt(gapLevel(i));
            const Cost byRoles = rolesAt(gapLevel(i));
            result.gapLower[i] = std::max(relaxed, byRoles);
            if(relaxed >= result.upper[i].cost)
                result.gapProof[i] = GapProof::Relaxed;
            else if(byRoles >= result.upper[i].cost)
                result.gapProof[i] = GapProof::Roles;
        });
    };
    boundGaps();

    // 3. Open gaps (and an uncertified fastest point): the cheapest balanced
    // role configuration at the gap's level either reaches the achieved cost
    // (the gap closes) or, scheduled (scheduleRoles), may be a new achieved
    // point inside the gap. Repeat while points are found.
    struct Balanced
    {
        bool complete = false;
        Cost value = kInfCost;
        Cost lagrange = std::numeric_limits<Cost>::min(); ///< Lagrangian bound, when computed
        std::vector<Cost> multipliers;                     ///< and the multipliers that give it
        std::optional<std::pair<FrontPoint, Plan>> scheduled;
    };
    std::map<Time, Balanced> cache;
    std::set<std::pair<Cost, Time>> searched, closedBySearch; // gaps by (cost of the left point, makespan of the right one)
    const auto balancedAt = [&](Time T) -> const Balanced& {
        return cache.at(T);
    };
    const auto refineUntil = std::chrono::steady_clock::now() +
                             std::chrono::duration_cast<std::chrono::steady_clock::duration>(std::chrono::duration<double>(options.refineSeconds));
    // After the gaps are recomputed, proofs already established for a gap's
    // level (cached bounds) or for its two ends (searches) apply again.
    const auto reapply = [&] {
        result.gapMultipliers.resize(result.gapProof.size());
        for(std::size_t i = 0; i < result.gapProof.size(); ++i)
        {
            if(result.gapProof[i] != GapProof::Open)
                continue;
            if(closedBySearch.contains({result.upper[i].cost, result.upper[i + 1].makespan}))
            {
                result.gapProof[i] = GapProof::Search;
                result.gapLower[i] = std::max(result.gapLower[i], result.upper[i].cost);
                continue;
            }
            const auto it = cache.find(gapLevel(i));
            if(it == cache.end())
                continue;
            const Balanced& b = it->second;
            if(b.lagrange > std::numeric_limits<Cost>::min())
                result.gapLower[i] = std::max(result.gapLower[i], b.lagrange);
            if(b.lagrange >= result.upper[i].cost)
            {
                result.gapProof[i] = GapProof::Lagrangian;
                result.gapMultipliers[i] = b.multipliers;
            }
            else if(b.complete)
            {
                result.gapLower[i] = std::max(result.gapLower[i], b.value);
                if(b.value >= result.upper[i].cost)
                    result.gapProof[i] = GapProof::Balanced;
            }
        }
    };
    for(int round = 0; round < 64 && std::chrono::steady_clock::now() < refineUntil; ++round)
    {
        std::vector<Time> wanted;
        if(result.fastestLower < result.upper.front().makespan)
            wanted.push_back((result.upper.front().makespan - 1) / r.makespanPerLevel);
        for(std::size_t i = 0; i < result.gapProof.size(); ++i)
            if(result.gapProof[i] == GapProof::Open)
                wanted.push_back(gapLevel(i));
        std::ranges::sort(wanted);
        wanted.erase(std::unique(wanted.begin(), wanted.end()), wanted.end());
        std::erase_if(wanted, [&](Time T) { return cache.contains(T); });
        // The Lagrangian bound first: polynomial, and enough for most gaps.
        std::map<Time, Cost> target;
        for(std::size_t i = 0; i < result.gapProof.size(); ++i)
            if(result.gapProof[i] == GapProof::Open)
                target[gapLevel(i)] = std::max(target[gapLevel(i)], result.upper[i].cost);
        std::vector<Balanced> computed(wanted.size());
        parallelFor(wanted.size(), threads, [&](std::size_t k) {
            if(std::chrono::steady_clock::now() >= refineUntil)
                return; // out of time: the level stays incomplete
            if(const auto it = target.find(wanted[k]); it != target.end())
            {
                LagrangianBound lagrange = lagrangianRoles(r, wanted[k], it->second);
                computed[k].lagrange = lagrange.value;
                computed[k].multipliers = std::move(lagrange.multipliers);
                if(computed[k].lagrange >= it->second)
                {
                    computed[k].complete = false; // not the optimum, only a bound
                    return;
                }
            }
            // Bound on the planes still to come: the role relaxation per plane.
            const Time T = wanted[k];
            const auto remaining = remainingPlanesBound(r, roles, T);
            const auto it = target.find(T);
            const BalancedRoles program(r, Gfill, T, options.roleStates, options.roleWork, it == target.end() ? kInfCost : it->second, &remaining);
            Balanced& b = computed[k];
            b.complete = program.complete();
            b.value = program.value();
            if(!program.optimal() || isInf(b.value))
                return;
            if(auto plan = scheduleRoles(instance, r, program.reconstruct()))
            {
                const PlanCheck check = checkPlan(instance, *plan);
                b.scheduled.emplace(FrontPoint{check.cost, check.makespan}, std::move(*plan));
            }
        });
        for(std::size_t k = 0; k < wanted.size(); ++k)
            cache.emplace(wanted[k], std::move(computed[k]));
        stats.exactCalls += wanted.size();

        // New achieved points inside gaps, or faster than the fastest.
        bool added = false;
        const auto offer = [&](const Balanced& b, Time below) {
            if(b.scheduled && b.scheduled->first.makespan < below &&
               std::ranges::none_of(candidates, [&](const auto& c) { return c.first == b.scheduled->first; }))
            {
                candidates.push_back(*b.scheduled);
                added = true;
            }
        };
        if(result.fastestLower < result.upper.front().makespan)
        {
            const Balanced& b = balancedAt((result.upper.front().makespan - 1) / r.makespanPerLevel);
            if(b.complete && isInf(b.value))
            {
                result.fastestLower = result.upper.front().makespan;
                result.fastestProof = GapProof::Balanced;
            }
            else
                offer(b, result.upper.front().makespan);
        }
        result.gapMultipliers.resize(result.gapProof.size());
        for(std::size_t i = 0; i < result.gapProof.size(); ++i)
        {
            if(result.gapProof[i] != GapProof::Open)
                continue;
            const Balanced& b = balancedAt(gapLevel(i));
            if(b.lagrange > std::numeric_limits<Cost>::min())
                result.gapLower[i] = std::max(result.gapLower[i], b.lagrange);
            if(b.lagrange >= result.upper[i].cost)
            {
                result.gapProof[i] = GapProof::Lagrangian;
                result.gapMultipliers[i] = b.multipliers;
                continue;
            }
            if(!b.complete)
                continue;
            result.gapLower[i] = std::max(result.gapLower[i], b.value);
            if(b.value >= result.upper[i].cost)
                result.gapProof[i] = GapProof::Balanced;
            else
                offer(b, result.upper[i + 1].makespan);
        }
        // Last resort, when the bounds found no new point: the exact search over
        // role configurations (Corollary 6.10), gap by gap.
        if(!added)
        {
            std::vector<std::pair<std::size_t, Time>> todo; // (gap index or npos for the fastest point, level)
            constexpr std::size_t fastest = static_cast<std::size_t>(-1);
            if(result.fastestLower < result.upper.front().makespan)
                todo.emplace_back(fastest, (result.upper.front().makespan - 1) / r.makespanPerLevel);
            for(std::size_t i = 0; i < result.gapProof.size(); ++i)
                if(result.gapProof[i] == GapProof::Open && !searched.contains({result.upper[i].cost, result.upper[i + 1].makespan}))
                    todo.emplace_back(i, gapLevel(i));
            std::vector<GapSearch> outcomes(todo.size());
            parallelFor(todo.size(), threads, [&](std::size_t k) {
                if(std::chrono::steady_clock::now() >= refineUntil)
                {
                    outcomes[k].outcome = GapSearch::Outcome::Incomplete;
                    return;
                }
                const auto [i, T] = todo[k];
                const Cost below = i == fastest ? kInfCost : result.upper[i].cost;
                const Time makespanBelow = i == fastest ? result.upper.front().makespan : result.upper[i + 1].makespan;
                outcomes[k] = searchGap(instance, r, Gfill, roles, T, below, makespanBelow, options.searchWork, refineUntil);
            });
            for(std::size_t k = 0; k < todo.size(); ++k)
            {
                const auto i = todo[k].first;
                const GapSearch& g = outcomes[k];
                if(i != fastest)
                    searched.insert({result.upper[i].cost, result.upper[i + 1].makespan});
                if(g.outcome == GapSearch::Outcome::Found && std::ranges::none_of(candidates, [&](const auto& c) { return c.first == g.found->first; }))
                {
                    candidates.push_back(*g.found);
                    added = true;
                }
                else if(g.outcome == GapSearch::Outcome::Closed)
                {
                    if(i == fastest)
                    {
                        result.fastestLower = result.upper.front().makespan;
                        result.fastestProof = GapProof::Search;
                    }
                    else
                    {
                        result.gapProof[i] = GapProof::Search;
                        result.gapLower[i] = std::max(result.gapLower[i], result.upper[i].cost);
                        closedBySearch.insert({result.upper[i].cost, result.upper[i + 1].makespan});
                    }
                }
            }
            stats.exactCalls += todo.size();
        }
        if(!added)
            break;
        rebuildUpper();
        boundGaps();
        reapply();
        // Gaps closed by the balanced bound in an earlier round stay closed
        // when they are unchanged: the cache answers them at once next round.
    }

    result.openReason.assign(result.gapProof.size(), BracketResult::OpenReason::None);
    for(std::size_t i = 0; i < result.gapProof.size(); ++i)
        if(result.gapProof[i] == GapProof::Open)
        {
            const auto it = cache.find(gapLevel(i));
            const bool complete = it != cache.end() && it->second.complete;
            result.openReason[i] = complete ? BracketResult::OpenReason::Unscheduled : BracketResult::OpenReason::Incomplete;
        }
    if(options.plans)
        for(const FrontPoint& point : result.upper)
            for(const auto& c : candidates)
                if(c.first == point)
                {
                    result.plans.push_back(c.second);
                    break;
                }
    stats.secondsExact = std::chrono::duration<double>(std::chrono::steady_clock::now() - start).count();
    return result;
}
} // namespace zeno
