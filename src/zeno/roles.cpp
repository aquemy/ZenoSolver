#include <zeno/roles.hpp>

#include <algorithm>
#include <functional>
#include <iterator>
#include <limits>
#include <map>
#include <numeric>
#include <stdexcept>
#include <unordered_map>

namespace zeno
{
namespace
{
std::size_t at(int v) { return static_cast<std::size_t>(v); }

struct KeyHash
{
    std::size_t operator()(const std::pair<std::vector<int>, int>& key) const noexcept
    {
        std::size_t h = std::hash<int>{}(key.second);
        for(int v : key.first)
            h = h * 1000003u ^ std::hash<int>{}(v + 1024);
        return h;
    }
};
} // namespace

BalancedRoles::BalancedRoles(const ReducedInstance& r, const OnePlaneTable& fill, Time T, std::size_t stateLimit, std::size_t workLimit,
                             Cost target, const std::vector<std::vector<Cost>>* remaining)
    : r_(r)
    , fill_(fill)
    , T_(T)
    , target_(target)
{
    const int n = r.n(), s = r.landings(), links = r.t - r.p;
    // Plane imbalances: every Delta with ||Delta||_1 <= t - p whose
    // drop-offs and pick-ups fit in T.
    std::vector<int> delta(at(n), 0);
    std::function<void(int, int, Time, Cost)> enumerate = [&](int i, int left, Time load, Cost cost) {
        if(!complete_)
            return;
        if(i == n)
        {
            options_.push_back({delta, load, cost, links - left});
            if(options_.size() > stateLimit)
                complete_ = false;
            return;
        }
        for(int v = -left; v <= left; ++v)
        {
            const Time w = v > 0 ? r.drop[at(i)] * v : r.pick[at(i)] * -v;
            if(load + w > T)
                continue;
            delta[at(i)] = v;
            enumerate(i + 1, left - (v < 0 ? -v : v), load + w, cost + r.c[at(i)] * (v < 0 ? -v : v));
        }
        delta[at(i)] = 0;
    };
    enumerate(0, links, 0, 0);
    if(!complete_)
        return;

    // Layers over planes: state (imbalance, landings so far).
    keys_.assign(at(r.p + 1), {});
    layers_.assign(at(r.p + 1), {});
    keys_[0].push_back({std::vector<int>(at(n), 0), 0});
    layers_[0].push_back({0, -1, 0, 0});
    std::size_t states = 1, work = 0;
    for(int k = 1; k <= r.p; ++k)
    {
        std::unordered_map<std::pair<std::vector<int>, int>, std::size_t, KeyHash> index;
        auto& keys = keys_[at(k)];
        auto& layer = layers_[at(k)];
        const auto& prevKeys = keys_[at(k - 1)];
        const auto& prev = layers_[at(k - 1)];
        const int planesLeft = r.p - k; // planes after this one, at least one landing each
        for(std::size_t st = 0; st < prev.size(); ++st)
        {
            const auto& [v, j] = prevKeys[st];
            work += options_.size();
            if(work > workLimit)
            {
                complete_ = false;
                return;
            }
            for(std::size_t o = 0; o < options_.size(); ++o)
            {
                const Option& opt = options_[o];
                std::vector<int> next = v;
                int norm = 0;
                for(int i = 0; i < n; ++i)
                {
                    next[at(i)] += opt.delta[at(i)];
                    norm += next[at(i)] < 0 ? -next[at(i)] : next[at(i)];
                }
                // At most t - p links in all, and the last state must be 0.
                if(norm > links || (planesLeft == 0 && norm != 0))
                    continue;
                for(int cr = 1; j + opt.landings + cr + planesLeft <= s && cr <= fill.maxLandings(); cr += 2)
                {
                    const Cost crossings = fill(cr, T - opt.load);
                    if(isInf(crossings))
                        break;
                    const int landings = j + opt.landings + cr;
                    if(planesLeft == 0 && landings != s)
                        continue;
                    const Cost cost = prev[st].cost + opt.cost + crossings;
                    if(!isInf(target) &&
                       (cost >= target || (remaining && addCost(cost, (*remaining)[at(planesLeft)][at(s - landings)]) >= target)))
                        continue;
                    auto key = std::pair(next, landings);
                    auto it = index.find(key);
                    if(it == index.end())
                    {
                        index.emplace(key, layer.size());
                        keys.push_back(std::move(key));
                        layer.push_back({cost, static_cast<int>(o), cr, st});
                        if(++states > stateLimit)
                        {
                            complete_ = false;
                            return;
                        }
                    }
                    else if(cost < layer[it->second].cost)
                        layer[it->second] = {cost, static_cast<int>(o), cr, st};
                }
            }
        }
    }
    value_ = isInf(target) ? kInfCost : target;
    const auto& keys = keys_[at(r.p)];
    for(std::size_t st = 0; st < keys.size(); ++st)
        if(keys[st].second == s && std::ranges::all_of(keys[st].first, [](int x) { return x == 0; }) && layers_[at(r.p)][st].cost < value_)
        {
            value_ = layers_[at(r.p)][st].cost;
            final_ = st;
        }
}

RoleConfig BalancedRoles::reconstruct() const
{
    if(!optimal() || isInf(value_))
        throw std::invalid_argument("BalancedRoles::reconstruct: no configuration");
    RoleConfig config;
    std::size_t st = final_;
    for(int k = r_.p; k >= 1; --k)
    {
        const Entry& e = layers_[at(k)][st];
        const Option& opt = options_[at(e.option)];
        std::vector<int> drops, picks;
        for(int i = 0; i < r_.n(); ++i)
            for(int c = 0; c < (opt.delta[at(i)] < 0 ? -opt.delta[at(i)] : opt.delta[at(i)]); ++c)
                (opt.delta[at(i)] > 0 ? drops : picks).push_back(i);
        config.drops.push_back(std::move(drops));
        config.picks.push_back(std::move(picks));
        config.crossings.push_back(fill_.witness(e.crossings, T_ - opt.load));
        st = e.parent;
    }
    return config;
}

RoleRelaxation::RoleRelaxation(const ReducedInstance& r, Time maxLevel)
    : r_(r)
    , maxLevel_(maxLevel)
    , stairs_(at(r.maxGroup() + 1))
    , total_(r.fill, r.c, r.landings(), static_cast<Time>(r.p) * maxLevel, OnePlaneTable::Layout::Staircase)
{
    stairs_[0][0].push_back({0, 0});
    std::vector<Stair> candidates;
    for(int m = 1; m <= r.maxGroup(); ++m)
        for(int parity = 0; parity < 2; ++parity)
        {
            candidates.clear();
            const auto extend = [&](const std::vector<Stair>& from, const std::vector<Time>& weight) {
                for(int i = 0; i < r.n(); ++i)
                    for(const Stair& st : from)
                    {
                        const Time load = st.load + weight[at(i)];
                        if(load > maxLevel)
                            break;
                        candidates.push_back({load, st.cost + r.c[at(i)]});
                    }
            };
            extend(stairs_[at(m - 1)][at(1 - parity)], r.fill); // one more crossing
            extend(stairs_[at(m - 1)][at(parity)], r.low);      // one more drop-off or pick-up
            std::ranges::sort(candidates, [](const Stair& x, const Stair& y) { return x.load != y.load ? x.load < y.load : x.cost < y.cost; });
            auto& out = stairs_[at(m)][at(parity)];
            for(const Stair& st : candidates)
                if((out.empty() || st.cost < out.back().cost) && (out.empty() || out.back().load != st.load))
                    out.push_back(st);
        }
}

Cost RoleRelaxation::oddGroup(int m, Time T) const
{
    if(T < 0 || m < 1 || m > r_.maxGroup())
        return kInfCost;
    if(T > maxLevel_)
        throw std::invalid_argument("RoleRelaxation: level above the table");
    const auto& steps = stairs_[at(m)][1];
    const auto it = std::upper_bound(steps.begin(), steps.end(), T, [](Time v, const Stair& st) { return v < st.load; });
    return it == steps.begin() ? kInfCost : std::prev(it)->cost;
}

Cost RoleRelaxation::bound(Time T) const
{
    if(T < 0)
        return kInfCost;
    const int p = r_.p, s = r_.landings();
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
                const Cost g = oddGroup(m, T);
                if(!isInf(g))
                    next[at(j + m)] = std::min(next[at(j + m)], best[at(j)] + g);
            }
        }
        best.swap(next);
    }
    return std::max(best[at(s)], total_(s, static_cast<Time>(p) * T));
}

std::vector<std::vector<Cost>> remainingPlanesBound(const ReducedInstance& r, const RoleRelaxation& roles, Time T)
{
    std::vector<std::vector<Cost>> remaining(at(r.p + 1), std::vector<Cost>(at(r.landings() + 1), kInfCost));
    remaining[0][0] = 0;
    for(int q = 1; q <= r.p; ++q)
        for(int j = 0; j <= r.landings(); ++j)
            for(int m = 1; m <= std::min(j, r.maxGroup()); ++m)
                remaining[at(q)][at(j)] = std::min(remaining[at(q)][at(j)], addCost(remaining[at(q - 1)][at(j - m)], roles.oddGroup(m, T)));
    return remaining;
}

namespace
{
/// The Lagrangian value at mu, and (optionally) a subgradient: drop-offs
/// minus pick-ups per city in a minimiser.
Cost lagrangianEvaluate(const ReducedInstance& r, Time T, const std::vector<Cost>& mu, std::size_t cellLimit, std::vector<Cost>* subgradient)
{
    const int n = r.n(), M = r.maxGroup(), s = r.landings();
    if(T < 0)
        return kInfCost;
    const auto W = static_cast<std::size_t>(T + 1);
    if(2 * at(M + 1) * W > cellLimit)
        return std::numeric_limits<Cost>::min();
    // H[par][m][w]: cheapest m landings of exact load w with crossing parity par.
    std::vector<Cost> H(2 * at(M + 1) * W, kInfCost);
    const auto cell = [&](int par, int m, std::size_t w) -> Cost& { return H[(at(par) * at(M + 1) + at(m)) * W + w]; };
    cell(0, 0, 0) = 0;
    const auto relax = [&](int par, int m, std::size_t w, int from, Time weight, Cost cost) {
        if(static_cast<std::size_t>(weight) > w)
            return;
        const Cost before = cell(from, m - 1, w - static_cast<std::size_t>(weight));
        if(!isInf(before))
            cell(par, m, w) = std::min(cell(par, m, w), before + cost);
    };
    for(int m = 1; m <= M; ++m)
        for(int par = 0; par < 2; ++par)
            for(std::size_t w = 0; w < W; ++w)
                for(int x = 0; x < n; ++x)
                {
                    relax(par, m, w, 1 - par, r.fill[at(x)], r.c[at(x)]);
                    relax(par, m, w, par, r.drop[at(x)], r.c[at(x)] + mu[at(x)]);
                    relax(par, m, w, par, r.pick[at(x)], r.c[at(x)] - mu[at(x)]);
                }
    std::vector<Cost> group(at(M + 1), kInfCost);
    std::vector<std::size_t> groupLoad(at(M + 1), 0);
    for(int m = 1; m <= M; ++m)
        for(std::size_t w = 0; w < W; ++w)
            if(cell(1, m, w) < group[at(m)])
            {
                group[at(m)] = cell(1, m, w);
                groupLoad[at(m)] = w;
            }
    std::vector<std::vector<Cost>> plan(at(r.p + 1), std::vector<Cost>(at(s + 1), kInfCost));
    std::vector<std::vector<int>> size(at(r.p + 1), std::vector<int>(at(s + 1), 0));
    plan[0][0] = 0;
    for(int k = 1; k <= r.p; ++k)
        for(int j = 0; j < s; ++j)
            if(!isInf(plan[at(k - 1)][at(j)]))
                for(int m = 1; m <= M && j + m <= s; ++m)
                    if(!isInf(group[at(m)]) && plan[at(k - 1)][at(j)] + group[at(m)] < plan[at(k)][at(j + m)])
                    {
                        plan[at(k)][at(j + m)] = plan[at(k - 1)][at(j)] + group[at(m)];
                        size[at(k)][at(j + m)] = m;
                    }
    const Cost value = plan[at(r.p)][at(s)];
    if(isInf(value) || !subgradient)
        return value;
    subgradient->assign(at(n), 0);
    int j = s;
    for(int k = r.p; k >= 1; --k)
    {
        int m = size[at(k)][at(j)];
        j -= m;
        int par = 1;
        std::size_t w = groupLoad[at(m)];
        for(; m > 0; --m)
        {
            bool found = false;
            const Cost here = cell(par, m, w);
            for(int x = 0; x < n && !found; ++x)
            {
                const auto attempt = [&](int from, Time weight, Cost cost, int dg) {
                    if(found || static_cast<std::size_t>(weight) > w)
                        return;
                    const Cost before = cell(from, m - 1, w - static_cast<std::size_t>(weight));
                    if(!isInf(before) && before + cost == here)
                    {
                        (*subgradient)[at(x)] += dg;
                        par = from;
                        w -= static_cast<std::size_t>(weight);
                        found = true;
                    }
                };
                attempt(1 - par, r.fill[at(x)], r.c[at(x)], 0);
                attempt(par, r.drop[at(x)], r.c[at(x)] + mu[at(x)], 1);
                attempt(par, r.pick[at(x)], r.c[at(x)] - mu[at(x)], -1);
            }
            if(!found)
                throw std::logic_error("lagrangianRoles: inconsistent table");
        }
    }
    return value;
}
} // namespace

Cost lagrangianValue(const ReducedInstance& r, Time T, const std::vector<Cost>& mu, std::size_t cellLimit)
{
    if(mu.size() != at(r.n()))
        throw std::invalid_argument("lagrangianValue: one multiplier per city is required");
    return lagrangianEvaluate(r, T, mu, cellLimit, nullptr);
}

LagrangianBound lagrangianRoles(const ReducedInstance& r, Time T, Cost target, int iterations, std::size_t cellLimit)
{
    const int n = r.n();
    std::vector<Cost> mu(at(n), 0), g;
    const Cost bound = static_cast<Cost>(r.landings()) * *std::ranges::max_element(r.c) + 1;
    LagrangianBound best{std::numeric_limits<Cost>::min(), mu};
    for(int it = 0; it < iterations; ++it)
    {
        const Cost value = lagrangianEvaluate(r, T, mu, cellLimit, &g);
        if(value == std::numeric_limits<Cost>::min())
            return best; // too large for the dense knapsack
        if(value > best.value)
            best = {value, mu};
        if(isInf(value) || best.value >= target)
            break;
        Cost norm = 0;
        for(Cost v : g)
            norm += v * v;
        if(norm == 0)
            break; // the minimiser is balanced: the bound is the balanced optimum
        // Polyak step towards the target, at least one unit; multipliers stay
        // within [-bound, bound] (beyond it no landing pays off, and every cost
        // of the tables stays far from overflow).
        const Cost gap = isInf(target) ? 1 : target - value;
        const Cost step = std::clamp<Cost>(gap / norm, 1, bound);
        for(int x = 0; x < n; ++x)
            mu[at(x)] = std::clamp<Cost>(mu[at(x)] + step * g[at(x)], -bound, bound);
    }
    return best;
}

std::optional<Plan> scheduleRoles(const Instance& instance, const ReducedInstance& r, const RoleConfig& config, std::size_t budget)
{
    const std::size_t p = config.drops.size();
    const int goal = instance.n() + 1;
    const auto location = [&](int city) { return r.original[at(city)] + 1; };
    const auto west = [&](int city) { return instance.d[at(r.original[at(city)])]; };
    const auto east = [&](int city) { return instance.dbar[at(r.original[at(city)])]; };

    std::size_t passengers = 0;
    for(std::size_t k = 0; k < p; ++k)
    {
        if(config.crossings[k].size() % 2 == 0)
            return std::nullopt;
        passengers += config.drops[k].size() + (config.crossings[k].size() + 1) / 2;
    }
    if(passengers != static_cast<std::size_t>(instance.t))
        return std::nullopt;

    // Current orders and matching: drops[k] and picks[k] in order; match[k][l]
    // = (plane, position) of the drop-off whose passenger pick-up l collects.
    std::vector<std::vector<int>> drops = config.drops, picks = config.picks;
    std::vector<std::vector<std::pair<std::size_t, std::size_t>>> match(p);

    const auto evaluate = [&](Plan* out) -> Time {
        // Drop-offs never wait: availability of each dropped passenger.
        std::vector<std::vector<Time>> available(p);
        std::vector<Time> phase1(p, 0);
        for(std::size_t k = 0; k < p; ++k)
        {
            Time now = 0;
            for(int x : drops[k])
            {
                available[k].push_back(now + west(x));
                now += 2 * west(x);
            }
            phase1[k] = now;
        }
        Time makespan = 0;
        std::vector<std::vector<int>> dropPassenger(p);
        int next = 0;
        if(out)
        {
            out->planes.assign(p, {});
            for(std::size_t k = 0; k < p; ++k)
                for(std::size_t j = 0; j < drops[k].size(); ++j)
                    dropPassenger[k].push_back(next++);
        }
        for(std::size_t k = 0; k < p; ++k)
        {
            auto* legs = out ? &out->planes[k] : nullptr;
            Time now = 0;
            for(std::size_t j = 0; j < drops[k].size(); ++j)
            {
                const int x = drops[k][j];
                if(legs)
                {
                    legs->push_back({0, location(x), now, now + west(x), dropPassenger[k][j]});
                    legs->push_back({location(x), 0, now + west(x), now + 2 * west(x), -1});
                }
                now += 2 * west(x);
            }
            const auto& cr = config.crossings[k];
            for(std::size_t i = 0; i < cr.size(); ++i)
            {
                const int x = cr[i];
                if(legs)
                {
                    if(i % 2 == 0)
                    {
                        const int passenger = next++;
                        legs->push_back({0, location(x), now, now + west(x), passenger});
                        legs->push_back({location(x), goal, now + west(x), now + west(x) + east(x), passenger});
                    }
                    else
                    {
                        legs->push_back({goal, location(x), now, now + east(x), -1});
                        legs->push_back({location(x), 0, now + east(x), now + east(x) + west(x), -1});
                    }
                }
                now += west(x) + east(x);
            }
            for(std::size_t l = 0; l < picks[k].size(); ++l)
            {
                const int y = picks[k][l];
                const auto [u, j] = match[k][l];
                const Time arrive = now + east(y);
                const Time leave = std::max(arrive, available[u][j]);
                if(legs)
                {
                    legs->push_back({goal, location(y), now, arrive, -1});
                    legs->push_back({location(y), goal, leave, leave + east(y), dropPassenger[u][j]});
                }
                now = leave + east(y);
            }
            makespan = std::max(makespan, now);
        }
        return makespan;
    };

    // Initial matching: per city, pick-ups in plane order take drop-offs in plane order.
    const auto matchInOrder = [&] {
        std::map<int, std::vector<std::pair<std::size_t, std::size_t>>> pool;
        for(std::size_t k = 0; k < p; ++k)
            for(std::size_t j = 0; j < drops[k].size(); ++j)
                pool[drops[k][j]].push_back({k, j});
        std::map<int, std::size_t> used;
        for(std::size_t k = 0; k < p; ++k)
        {
            match[k].clear();
            for(int y : picks[k])
            {
                auto& candidates = pool[y];
                if(used[y] >= candidates.size())
                    return false;
                match[k].push_back(candidates[used[y]++]);
            }
        }
        return true;
    };
    if(!matchInOrder())
        return std::nullopt;

    // Local search: start from availability-sorted pick-ups and improve by
    // swapping drop-off orders, pick-up orders and matched passengers, up to
    // `budget` evaluations.
    const auto sortPicks = [&] {
        for(std::size_t k = 0; k < p; ++k)
        {
            std::vector<std::size_t> idx(picks[k].size());
            std::iota(idx.begin(), idx.end(), 0);
            std::vector<Time> avail;
            for(const auto& [u, j] : match[k])
            {
                Time t0 = 0;
                for(std::size_t q = 0; q < j; ++q)
                    t0 += 2 * west(drops[u][q]);
                avail.push_back(t0 + west(drops[u][j]));
            }
            std::ranges::stable_sort(idx, [&](std::size_t a, std::size_t b) { return avail[a] < avail[b]; });
            std::vector<int> np;
            std::vector<std::pair<std::size_t, std::size_t>> nm;
            for(std::size_t i : idx)
            {
                np.push_back(picks[k][i]);
                nm.push_back(match[k][i]);
            }
            picks[k] = std::move(np);
            match[k] = std::move(nm);
        }
    };
    sortPicks();
    Time best = evaluate(nullptr);
    std::size_t evaluations = 1;
    bool improved = true;
    while(improved && evaluations < budget)
    {
        improved = false;
        const auto attempt = [&](const auto& apply, const auto& undo) {
            apply();
            const Time m = evaluate(nullptr);
            ++evaluations;
            if(m < best)
            {
                best = m;
                improved = true;
                return true;
            }
            undo();
            return false;
        };
        for(std::size_t k = 0; k < p && evaluations < budget; ++k)
        {
            // Swap two drop-offs of plane k (renumber the matches pointing at them).
            for(std::size_t a = 0; a < drops[k].size(); ++a)
                for(std::size_t b = a + 1; b < drops[k].size(); ++b)
                {
                    const auto swapDrops = [&] {
                        std::swap(drops[k][a], drops[k][b]);
                        for(auto& m : match)
                            for(auto& [u, j] : m)
                                if(u == k && (j == a || j == b))
                                    j = j == a ? b : a;
                    };
                    attempt(swapDrops, swapDrops);
                }
            // Swap two pick-ups of plane k (with their matches).
            for(std::size_t a = 0; a < picks[k].size(); ++a)
                for(std::size_t b = a + 1; b < picks[k].size(); ++b)
                {
                    const auto swapPicks = [&] {
                        std::swap(picks[k][a], picks[k][b]);
                        std::swap(match[k][a], match[k][b]);
                    };
                    attempt(swapPicks, swapPicks);
                }
        }
        // Exchange the passengers of two pick-ups in the same city.
        for(std::size_t k = 0; k < p && evaluations < budget; ++k)
            for(std::size_t a = 0; a < picks[k].size(); ++a)
                for(std::size_t k2 = k; k2 < p; ++k2)
                    for(std::size_t b = (k2 == k ? a + 1 : 0); b < picks[k2].size(); ++b)
                        if(picks[k][a] == picks[k2][b])
                        {
                            const auto exchange = [&] { std::swap(match[k][a], match[k2][b]); };
                            attempt(exchange, exchange);
                        }
    }
    Plan plan;
    evaluate(&plan);
    const PlanCheck check = checkPlan(instance, plan);
    if(!check.ok || check.makespan != best)
        throw std::logic_error("scheduleRoles: the schedule fails its check: " + (check.ok ? std::string("makespan") : check.error));
    return plan;
}
} // namespace zeno
