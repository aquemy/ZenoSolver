#include <zeno/ns_search.hpp>

#include <algorithm>
#include <functional>
#include <map>
#include <numeric>
#include <stdexcept>

namespace zeno
{
namespace
{
std::size_t at(int v) { return static_cast<std::size_t>(v); }

struct Durations
{
    const Instance& instance;
    const ReducedInstance& r;
    Time west(int city) const { return instance.d[at(r.original[at(city)])]; }
    Time east(int city) const { return instance.dbar[at(r.original[at(city)])]; }
    int location(int city) const { return r.original[at(city)] + 1; }
};

/// Template makespan, and the plan when `out` is given.
Time runTemplate(const Durations& dur, const TemplateSchedule& s, Plan* out)
{
    const std::size_t p = s.drops.size();
    const int goal = dur.instance.n() + 1;
    std::vector<std::vector<Time>> available(p);
    std::vector<std::vector<int>> dropPassenger(p);
    int next = 0;
    for(std::size_t k = 0; k < p; ++k)
    {
        Time now = 0;
        for(int x : s.drops[k])
        {
            available[k].push_back(now + dur.west(x));
            now += 2 * dur.west(x);
            dropPassenger[k].push_back(next++);
        }
    }
    if(out)
        out->planes.assign(p, {});
    Time makespan = 0;
    for(std::size_t k = 0; k < p; ++k)
    {
        auto* legs = out ? &out->planes[k] : nullptr;
        Time now = 0;
        for(std::size_t j = 0; j < s.drops[k].size(); ++j)
        {
            const int x = s.drops[k][j];
            if(legs)
            {
                legs->push_back({0, dur.location(x), now, now + dur.west(x), dropPassenger[k][j]});
                legs->push_back({dur.location(x), 0, now + dur.west(x), now + 2 * dur.west(x), -1});
            }
            now += 2 * dur.west(x);
        }
        for(std::size_t i = 0; i < s.crossings[k].size(); ++i)
        {
            const int x = s.crossings[k][i];
            if(legs)
            {
                if(i % 2 == 0)
                {
                    const int passenger = next++;
                    legs->push_back({0, dur.location(x), now, now + dur.west(x), passenger});
                    legs->push_back({dur.location(x), goal, now + dur.west(x), now + dur.west(x) + dur.east(x), passenger});
                }
                else
                {
                    legs->push_back({goal, dur.location(x), now, now + dur.east(x), -1});
                    legs->push_back({dur.location(x), 0, now + dur.east(x), now + dur.east(x) + dur.west(x), -1});
                }
            }
            now += dur.west(x) + dur.east(x);
        }
        for(std::size_t l = 0; l < s.picks[k].size(); ++l)
        {
            const int y = s.picks[k][l];
            const auto [u, j] = s.match[k][l];
            const Time arrive = now + dur.east(y);
            const Time leave = std::max(arrive, available[u][j]);
            if(legs)
            {
                legs->push_back({goal, dur.location(y), now, arrive, -1});
                legs->push_back({dur.location(y), goal, leave, leave + dur.east(y), dropPassenger[u][j]});
            }
            now = leave + dur.east(y);
        }
        makespan = std::max(makespan, now);
    }
    return makespan;
}
} // namespace

Time templateMakespan(const Instance& instance, const ReducedInstance& r, const TemplateSchedule& schedule)
{
    return runTemplate({instance, r}, schedule, nullptr);
}

Plan templatePlan(const Instance& instance, const ReducedInstance& r, const TemplateSchedule& schedule)
{
    Plan plan;
    runTemplate({instance, r}, schedule, &plan);
    return plan;
}

ExactSchedule exactSchedule(const Instance& instance, const ReducedInstance& r, const RoleConfig& config, Time below, std::size_t budget,
                            Deadline deadline)
{
    ExactSchedule result;
    const Durations dur{instance, r};
    const std::size_t p = config.drops.size();
    // A valid configuration: odd crossings, t passengers, balanced.
    std::size_t passengers = 0;
    std::map<int, int> balance;
    Time lambda = 0;
    std::vector<Time> phaseEnd(p, 0); // end of drop-offs and crossings
    for(std::size_t k = 0; k < p; ++k)
    {
        if(config.crossings[k].size() % 2 == 0)
            return result;
        passengers += config.drops[k].size() + (config.crossings[k].size() + 1) / 2;
        Time load = 0;
        for(int x : config.drops[k]) { load += 2 * dur.west(x); ++balance[x]; }
        for(int x : config.crossings[k]) load += dur.west(x) + dur.east(x);
        phaseEnd[k] = load;
        for(int y : config.picks[k]) { load += 2 * dur.east(y); --balance[y]; }
        lambda = std::max(lambda, load);
    }
    if(passengers != static_cast<std::size_t>(instance.t) || std::ranges::any_of(balance, [](const auto& b) { return b.second != 0; }))
        return result;
    if(lambda >= below)
        return result; // every schedule takes at least the largest load

    std::vector<std::vector<int>> drops = config.drops;
    for(auto& d : drops)
        std::ranges::sort(d);
    // Pick-ups by city: (plane, index in config.picks[plane]).
    std::map<int, std::vector<std::pair<std::size_t, std::size_t>>> picksAt;
    for(std::size_t k = 0; k < p; ++k)
        for(std::size_t l = 0; l < config.picks[k].size(); ++l)
            picksAt[config.picks[k][l]].push_back({k, l});
    std::vector<int> cities;
    for(const auto& [x, list] : picksAt)
        cities.push_back(x);

    std::size_t work = 0;
    bool found = false;
    std::vector<std::vector<Time>> available(p);
    // assigned[k][l]: the drop-off (plane, position) of pick-up l of plane k.
    std::vector<std::vector<std::pair<std::size_t, std::size_t>>> assigned(p);
    for(std::size_t k = 0; k < p; ++k)
        assigned[k].assign(config.picks[k].size(), {0, 0});

    // With drop orders and matching fixed: each plane's pick-ups in order of
    // release (availability minus the flight there), optimal for 1|r_j|Cmax.
    const auto evaluateMatching = [&] {
        if(++work % 4096 == 0 && std::chrono::steady_clock::now() >= deadline)
            work = budget + 1; // out of time: give up
        Time makespan = 0;
        for(std::size_t k = 0; k < p && makespan < below; ++k)
        {
            std::vector<std::size_t> order(config.picks[k].size());
            std::iota(order.begin(), order.end(), std::size_t{0});
            const auto release = [&](std::size_t l) {
                const auto [u, j] = assigned[k][l];
                return available[u][j] - dur.east(config.picks[k][l]);
            };
            std::ranges::sort(order, [&](std::size_t a, std::size_t b) { return release(a) < release(b); });
            Time now = phaseEnd[k];
            for(std::size_t l : order)
            {
                const auto [u, j] = assigned[k][l];
                const int y = config.picks[k][l];
                now = std::max(now + dur.east(y), available[u][j]) + dur.east(y);
            }
            makespan = std::max(makespan, now);
        }
        if(makespan < below)
        {
            found = true;
            TemplateSchedule s;
            s.drops = drops;
            s.crossings = config.crossings;
            s.picks.assign(p, {});
            s.match.assign(p, {});
            for(std::size_t k = 0; k < p; ++k)
            {
                std::vector<std::size_t> order(config.picks[k].size());
                std::iota(order.begin(), order.end(), std::size_t{0});
                const auto release = [&](std::size_t l) {
                    const auto [u, j] = assigned[k][l];
                    return available[u][j] - dur.east(config.picks[k][l]);
                };
                std::ranges::sort(order, [&](std::size_t a, std::size_t b) { return release(a) < release(b); });
                for(std::size_t l : order)
                {
                    s.picks[k].push_back(config.picks[k][l]);
                    s.match[k].push_back(assigned[k][l]);
                }
            }
            result.makespan = runTemplate(dur, s, nullptr);
            result.best = std::move(s);
        }
    };

    // Matching city by city: each pick-up gets a drop-off of another plane.
    std::function<void(std::size_t)> matchCity = [&](std::size_t ci) {
        if(found || work > budget)
            return;
        if(ci == cities.size())
        {
            evaluateMatching();
            return;
        }
        const int x = cities[ci];
        std::vector<std::pair<std::size_t, std::size_t>> dropsHere;
        for(std::size_t k = 0; k < p; ++k)
            for(std::size_t j = 0; j < drops[k].size(); ++j)
                if(drops[k][j] == x)
                    dropsHere.push_back({k, j});
        const auto& picksHere = picksAt[x];
        std::vector<std::size_t> perm(dropsHere.size());
        std::iota(perm.begin(), perm.end(), std::size_t{0});
        do
        {
            bool ok = true;
            for(std::size_t q = 0; q < picksHere.size() && ok; ++q)
                ok = dropsHere[perm[q]].first != picksHere[q].first;
            if(!ok)
                continue;
            for(std::size_t q = 0; q < picksHere.size(); ++q)
                assigned[picksHere[q].first][picksHere[q].second] = dropsHere[perm[q]];
            matchCity(ci + 1);
        } while(!found && work <= budget && std::next_permutation(perm.begin(), perm.end()));
    };

    // Drop-off orders, plane by plane (distinct permutations of each multiset).
    std::function<void(std::size_t)> orderPlane = [&](std::size_t k) {
        if(found || work > budget)
            return;
        if(k == p)
        {
            for(std::size_t u = 0; u < p; ++u)
            {
                available[u].clear();
                Time now = 0;
                for(int x : drops[u])
                {
                    available[u].push_back(now + dur.west(x));
                    now += 2 * dur.west(x);
                }
            }
            matchCity(0);
            return;
        }
        std::ranges::sort(drops[k]);
        do
            orderPlane(k + 1);
        while(!found && work <= budget && std::next_permutation(drops[k].begin(), drops[k].end()));
    };
    orderPlane(0);
    result.complete = found || work <= budget;
    return result;
}

GapSearch searchGap(const Instance& instance, const ReducedInstance& r, const OnePlaneTable& fill, const RoleRelaxation& roles, Time T,
                    Cost costBelow, Time makespanBelow, std::size_t budget, Deadline deadline)
{
    GapSearch result;
    const int n = r.n(), s = r.landings(), links = r.t - r.p, p = r.p;
    if(T < 0)
    {
        result.outcome = GapSearch::Outcome::Closed;
        return result;
    }

    // Plane contents: drop-offs D and pick-ups P (counts per city, at most
    // t - p in all: a plane's drop-offs and pick-ups belong to distinct links),
    // and an odd number of crossings at a Pareto point of the crossing table.
    struct Option
    {
        std::vector<int> drops, picks; // cities, with repetition
        std::vector<int> delta;        // drop-offs minus pick-ups per city
        int crossings = 0;
        Time crossingLoad = 0;
        Cost cost = 0;
        int landings = 0;
    };
    std::vector<Option> options;
    std::vector<int> D(at(n), 0), P(at(n), 0);
    std::function<void(int, int, Time, Cost)> roleParts = [&](int i, int left, Time load, Cost cost) {
        if(i == n)
        {
            Option base;
            for(int x = 0; x < n; ++x)
            {
                base.drops.insert(base.drops.end(), at(D[at(x)]), x);
                base.picks.insert(base.picks.end(), at(P[at(x)]), x);
                base.delta.push_back(D[at(x)] - P[at(x)]);
            }
            const int roleLandings = links - left;
            for(int cr = 1; roleLandings + cr <= r.maxGroup() && cr <= fill.maxLandings(); cr += 2)
                for(const auto& [crossingLoad, crossingCost] : fill.paretoPoints(cr, T - load))
                {
                    Option o = base;
                    o.crossings = cr;
                    o.crossingLoad = crossingLoad;
                    o.cost = cost + crossingCost;
                    o.landings = roleLandings + cr;
                    if(o.cost < costBelow)
                        options.push_back(std::move(o));
                }
            return;
        }
        for(int dI = 0; dI <= left; ++dI)
            for(int pI = 0; dI + pI <= left; ++pI)
            {
                const Time w = r.drop[at(i)] * dI + r.pick[at(i)] * pI;
                if(load + w > T)
                    continue;
                D[at(i)] = dI;
                P[at(i)] = pI;
                roleParts(i + 1, left - dI - pI, load + w, cost + r.c[at(i)] * (dI + pI));
            }
        D[at(i)] = P[at(i)] = 0;
    };
    roleParts(0, links, 0, 0);
    std::ranges::sort(options, [](const Option& a, const Option& b) { return a.cost < b.cost; });

    const auto remaining = remainingPlanesBound(r, roles, T);
    std::size_t work = 0;
    bool incomplete = false;
    std::vector<std::size_t> chosen;
    std::vector<int> v(at(n), 0);
    std::function<bool(int, std::size_t, int, Cost)> dfs = [&](int k, std::size_t from, int landings, Cost cost) -> bool {
        if(++work > budget || (work % 4096 == 0 && std::chrono::steady_clock::now() >= deadline))
        {
            work = budget + 1;
            incomplete = true;
            return false;
        }
        if(k == p)
        {
            if(landings != s || std::ranges::any_of(v, [](int x) { return x != 0; }))
                return false;
            RoleConfig config;
            for(std::size_t o : chosen)
            {
                config.drops.push_back(options[o].drops);
                config.picks.push_back(options[o].picks);
                config.crossings.push_back(fill.witness(options[o].crossings, options[o].crossingLoad));
            }
            ++result.configurations;
            const ExactSchedule schedule = exactSchedule(instance, r, config, makespanBelow, budget, deadline);
            if(!schedule.complete)
                incomplete = true;
            if(!schedule.best)
                return false;
            Plan plan = templatePlan(instance, r, *schedule.best);
            const PlanCheck check = checkPlan(instance, plan);
            if(!check.ok || check.makespan >= makespanBelow || check.cost >= costBelow)
                throw std::logic_error("searchGap: a found schedule fails its check");
            result.found.emplace(FrontPoint{check.cost, check.makespan}, std::move(plan));
            return true;
        }
        for(std::size_t o = from; o < options.size(); ++o)
        {
            const Option& opt = options[o];
            if(cost + opt.cost >= costBelow)
                break; // sorted by cost
            const int planesLeft = p - k - 1;
            const int after = landings + opt.landings;
            if(after + planesLeft > s)
                continue;
            if(addCost(cost + opt.cost, remaining[at(planesLeft)][at(s - after)]) >= costBelow)
                continue;
            int norm = 0;
            for(int i = 0; i < n; ++i)
            {
                const int x = v[at(i)] + opt.delta[at(i)];
                norm += x < 0 ? -x : x;
            }
            if(norm > links || (planesLeft == 0 && norm != 0))
                continue;
            for(int i = 0; i < n; ++i)
                v[at(i)] += opt.delta[at(i)];
            chosen.push_back(o);
            const bool hit = dfs(k + 1, o, after, cost + opt.cost);
            chosen.pop_back();
            for(int i = 0; i < n; ++i)
                v[at(i)] -= opt.delta[at(i)];
            if(hit)
                return true;
            if(incomplete && work > budget)
                return false;
        }
        return false;
    };
    const bool hit = dfs(0, 0, 0, 0);
    result.outcome = hit ? GapSearch::Outcome::Found : incomplete ? GapSearch::Outcome::Incomplete : GapSearch::Outcome::Closed;
    return result;
}
} // namespace zeno
