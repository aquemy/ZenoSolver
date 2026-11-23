// Unit and differential tests of the exact solver (library zeno_core).
//
// The reference is the enumeration oracle (tests/oracle/partitionEnum.hpp),
// which shares no code with the library: every landing multiset, every
// admissible partition.
#include <zeno/certificate.hpp>
#include <zeno/forest.hpp>
#include <zeno/ns.hpp>
#include <zeno/roles.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/reduce.hpp>
#include <zeno/solve.hpp>

#include "oracle/bruteForce.hpp"
#include "oracle/partitionEnum.hpp"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <numeric>
#include <random>
#include <sstream>
#include <string>
#include <vector>

namespace
{
int failures = 0;

void check(bool ok, const std::string& what)
{
    if(!ok)
    {
        if(++failures <= 20)
            std::cerr << "FAIL: " << what << "\n";
    }
}

std::string describe(const zeno::Instance& in)
{
    std::ostringstream out;
    out << "d=";
    for(auto v : in.d) out << v << ",";
    out << " c=";
    for(auto v : in.c) out << v << ",";
    out << " t=" << in.t << " p=" << in.p;
    return out.str();
}

oracle::partition::Instance toOracle(const zeno::Instance& in)
{
    return {in.d, in.c, in.t, in.p};
}

zeno::Instance randomInstance(std::mt19937& rng, int maxN, int maxT, int maxP, int maxS)
{
    std::uniform_int_distribution<int> pDist(1, maxP);
    zeno::Instance in;
    in.p = pDist(rng);
    in.t = std::uniform_int_distribution<int>(in.p, std::max(in.p, maxT))(rng);
    while(2 * in.t - in.p > maxS && in.t > in.p)
        --in.t;
    const int n = std::uniform_int_distribution<int>(1, maxN)(rng);
    std::uniform_int_distribution<int> value(0, 12), zero(0, 9);
    for(int i = 0; i < n; ++i)
    {
        in.d.push_back(zero(rng) == 0 ? 0 : value(rng) + 1);
        in.c.push_back(zero(rng) == 0 ? 0 : value(rng) + 1);
    }
    in.dbar = in.d;
    return in;
}

void testParetoFilter()
{
    const zeno::Front f = zeno::paretoFilter({{10, 5}, {8, 7}, {9, 7}, {10, 4}, {8, 9}, {3, 20}, {3, 20}});
    check(f == zeno::Front{{10, 4}, {8, 7}, {3, 20}}, "paretoFilter keeps the non-dominated points");
}

void testReduce()
{
    zeno::Instance in;
    in.d = {4, 2, 6, 6, 8, 2};
    in.c = {5, 9, 5, 3, 1, 7};
    in.dbar = in.d;
    in.t = 4;
    in.p = 2;
    const auto r = zeno::reduce(in);
    // Staircase by duration: (2,7) (4,5) (6,3) (8,1); (2,9) and (6,5) dominated.
    check(r.d == std::vector<zeno::Time>{1, 2, 3, 4}, "reduce: durations scaled by their gcd");
    check(r.c == std::vector<zeno::Cost>{7, 5, 3, 1}, "reduce: staircase costs");
    check(r.scale == 2, "reduce: scale is the gcd");
    check(r.original == std::vector<int>{5, 0, 3, 4}, "reduce: representatives");
    check(r.landings() == 6 && r.maxGroup() == 5 && r.maxTree() == 2, "reduce: sizes");
    check(r.lowestLevel() == 3 && r.highestLevel() == 12, "reduce: level range");
}

void testOnePlaneTable(std::mt19937& rng)
{
    for(int trial = 0; trial < 200; ++trial)
    {
        const int n = std::uniform_int_distribution<int>(1, 4)(rng);
        std::vector<zeno::Time> d;
        std::vector<zeno::Cost> c;
        for(int i = 0; i < n; ++i)
        {
            d.push_back(std::uniform_int_distribution<int>(0, 6)(rng));
            c.push_back(std::uniform_int_distribution<int>(0, 9)(rng));
        }
        const int M = 4;
        const zeno::Time maxT = 18;
        const zeno::OnePlaneTable G(d, c, M, maxT, zeno::OnePlaneTable::Layout::Dense);
        const zeno::OnePlaneTable stairs(d, c, M, maxT, zeno::OnePlaneTable::Layout::Staircase);
        // Brute force over all multisets of size m.
        for(int m = 0; m <= M; ++m)
            for(zeno::Time T = 0; T <= maxT; ++T)
            {
                zeno::Cost best = zeno::kInfCost;
                std::function<void(int, int, zeno::Time, zeno::Cost)> rec = [&](int from, int left, zeno::Time dur, zeno::Cost cost) {
                    if(left == 0)
                    {
                        if(dur <= T) best = std::min(best, cost);
                        return;
                    }
                    for(int i = from; i < n; ++i)
                        rec(i, left - 1, dur + d[static_cast<std::size_t>(i)], cost + c[static_cast<std::size_t>(i)]);
                };
                rec(0, m, 0, 0);
                check(G(m, T) == best, "OnePlaneTable G[" + std::to_string(m) + "][" + std::to_string(T) + "]");
                check(stairs(m, T) == best, "staircase G[" + std::to_string(m) + "][" + std::to_string(T) + "]");
                if(!zeno::isInf(best))
                    for(const auto* table : {&G, &stairs})
                    {
                        const auto w = table->witness(m, T);
                        zeno::Time load = 0;
                        zeno::Cost cost = 0;
                        for(int city : w)
                        {
                            load += d[static_cast<std::size_t>(city)];
                            cost += c[static_cast<std::size_t>(city)];
                        }
                        check(static_cast<int>(w.size()) == m && load <= T && cost == best, "witness realises G");
                    }
            }
    }
}

// L <= E <= U3 <= U at every level, E equals the oracle, and trees of
// maxTree planes suffice (the unrestricted DP gives the same values).
struct Sizes
{
    int n = 4, t = 7, p = 4, s = 10;
};

void testLevels(std::mt19937& rng, int trials, const Sizes& z)
{
    for(int trial = 0; trial < trials; ++trial)
    {
        const zeno::Instance in = randomInstance(rng, z.n, z.t, z.p, z.s);
        const auto r = zeno::reduce(in);
        const zeno::Time hi = r.highestLevel();
        const zeno::OnePlaneTable G(r.d, r.c, r.maxGroup(), hi);
        const auto oracleE = oracle::partition::levelValues(toOracle(in), hi * r.scale);
        for(zeno::Time T = 0; T <= hi; ++T)
        {
            const zeno::Cost L = zeno::relaxedCost(r, G, T);
            const zeno::Cost U = zeno::forestCost(r, G, T, 2);
            const zeno::Cost U3 = zeno::forestCost(r, G, T, 3);
            const zeno::Cost E = zeno::forestCost(r, G, T, r.maxTree());
            const zeno::Cost all = zeno::forestCost(r, G, T, r.p);
            const auto expected = oracleE[static_cast<std::size_t>(T * r.scale)];
            const zeno::Cost want = expected >= oracle::partition::kInf ? zeno::kInfCost : expected;
            const std::string where = describe(in) + " T=" + std::to_string(T);
            check(L <= E && E <= U3 && U3 <= U, "bracket order L <= E <= U3 <= U: " + where);
            check(E == want, "E(T) = oracle (" + std::to_string(E) + " vs " + std::to_string(want) + "): " + where);
            check(all == E, "trees beyond maxTree planes are useless: " + where);
        }
    }
}

void testFront(std::mt19937& rng, int trials, const Sizes& z)
{
    for(int trial = 0; trial < trials; ++trial)
    {
        const zeno::Instance in = randomInstance(rng, z.n, z.t, z.p, z.s);
        const auto expected = oracle::partition::paretoFront(toOracle(in));
        zeno::SolveOptions one;
        one.threads = 1;
        const auto single = zeno::solveFront(in, one).front;
        const auto multi = zeno::solveFront(in).front;
        // Every combination of level strategy and table layout gives the same front.
        for(auto strategy : {zeno::LevelStrategy::Sweep, zeno::LevelStrategy::Search})
            for(auto layout : {zeno::OnePlaneTable::Layout::Dense, zeno::OnePlaneTable::Layout::Staircase})
            {
                zeno::SolveOptions o;
                o.levels = strategy;
                o.table = layout;
                o.plans = strategy == zeno::LevelStrategy::Search;
                const auto other = zeno::solveFront(in, o);
                check(other.front == single, "strategy and layout do not change the front: " + describe(in));
                check(!o.plans || other.plans.size() == other.front.size(), "plans with the staircase table: " + describe(in));
            }
        std::vector<std::pair<zeno::Cost, zeno::Time>> got;
        for(auto it = single.rbegin(); it != single.rend(); ++it)
            got.emplace_back(it->cost, it->makespan);
        check(got == expected, "solveFront = oracle front: " + describe(in));
        check(single == multi, "solveFront does not depend on the thread count: " + describe(in));
    }
}

// Every front point comes with a plan that the independent checker accepts
// (solveFront throws otherwise), and the checker rejects broken plans.
void testPlans(std::mt19937& rng, int trials, const Sizes& z)
{
    zeno::SolveOptions options;
    options.plans = true;
    for(int trial = 0; trial < trials; ++trial)
    {
        const zeno::Instance in = randomInstance(rng, z.n, z.t, z.p, z.s);
        zeno::SolveResult result;
        try
        {
            result = zeno::solveFront(in, options);
        }
        catch(const std::exception& e)
        {
            check(false, std::string("plans: ") + e.what() + ": " + describe(in));
            continue;
        }
        check(result.plans.size() == result.front.size(), "one plan per front point: " + describe(in));
        for(std::size_t i = 0; i < result.plans.size(); ++i)
        {
            const auto ok = zeno::checkPlan(in, result.plans[i]);
            check(ok.ok && ok.cost == result.front[i].cost && ok.makespan == result.front[i].makespan, "plan realises its point: " + describe(in));
        }
        if(result.plans.empty())
            continue;
        // Mutations of the first plan must be rejected (or change the objectives).
        const zeno::Plan& plan = result.plans.front();
        const auto rejected = [&](const zeno::Plan& bad, const std::string& what) {
            const auto r = zeno::checkPlan(in, bad);
            check(!r.ok || r.cost != result.front.front().cost || r.makespan != result.front.front().makespan, "checker notices: " + what + ": " + describe(in));
        };
        for(std::size_t k = 0; k < plan.planes.size(); ++k)
        {
            if(plan.planes[k].empty())
                continue;
            zeno::Plan bad = plan;
            bad.planes[k].pop_back();
            rejected(bad, "a plane stops early");
            bad = plan;
            bad.planes[k].front().arrive += 1;
            rejected(bad, "a flight of the wrong duration");
            for(std::size_t l = 0; l < plan.planes[k].size(); ++l)
                if(plan.planes[k][l].passenger >= 0)
                {
                    bad = plan;
                    bad.planes[k][l].passenger = -1;
                    rejected(bad, "a passenger left behind");
                    break;
                }
        }
        zeno::Plan bad = plan;
        bad.planes.pop_back();
        rejected(bad, "a missing plane");
    }
}

// Certificates round-trip, are accepted, and are rejected once corrupted.
void testCertificates(std::mt19937& rng, int trials, const Sizes& z)
{
    zeno::SolveOptions options;
    options.plans = true;
    for(int trial = 0; trial < trials; ++trial)
    {
        const zeno::Instance in = randomInstance(rng, z.n, z.t, z.p, z.s);
        const auto result = zeno::solveFront(in, options);
        const zeno::Certificate cert = zeno::makeCertificate(in, result);
        std::stringstream text;
        zeno::writeCertificate(text, cert);
        const zeno::Certificate back = zeno::readCertificate(text);
        const auto report = zeno::checkCertificate(back);
        check(report.ok, "certificate accepted: " + describe(in) + (report.errors.empty() ? "" : ": " + report.errors.front()));
        check(back.front == cert.front && back.gaps == cert.gaps && back.instance.d == in.d, "certificate round trip: " + describe(in));

        const auto rejected = [&](zeno::Certificate bad, const std::string& what) {
            check(!zeno::checkCertificate(bad).ok, "corrupted certificate rejected (" + what + "): " + describe(in));
        };
        zeno::Certificate bad = cert;
        bad.front.front().cost -= 1;
        rejected(bad, "fastest point made cheaper");
        if(cert.front.size() >= 2)
        {
            bad = cert;
            bad.front.erase(bad.front.begin() + 1);
            bad.plans.erase(bad.plans.begin() + 1);
            bad.gaps.pop_back();
            rejected(bad, "a point removed");
            bad = cert;
            bad.front[1].makespan -= 1;
            rejected(bad, "a point made faster");
            for(std::size_t g = 0; g < cert.gaps.size(); ++g)
                if(cert.gaps[g] == zeno::GapBound::Forest)
                {
                    bad = cert;
                    bad.gaps[g] = zeno::GapBound::Relaxed;
                    rejected(bad, "a forest gap claimed by the relaxation");
                    bad = cert;
                    bad.assumptions = {"S"};
                    rejected(bad, "assumption A1 dropped");
                    break;
                }
        }
        bad = cert;
        bad.assumptions.clear();
        rejected(bad, "no assumptions");
    }
}

// The bracket of a symmetric instance: its upper front is the exact front
// (forests suffice and nothing waits), and its lower bounds lie below it.
void testBracketSymmetric(std::mt19937& rng, int trials, const Sizes& z)
{
    for(int trial = 0; trial < trials; ++trial)
    {
        const zeno::Instance in = randomInstance(rng, z.n, z.t, z.p, z.s);
        const auto exact = zeno::solveFront(in).front;
        const auto bracket = zeno::solveBracket(in);
        check(bracket.upper == exact, "symmetric bracket: upper front = exact front: " + describe(in));
        check(bracket.fastestLower <= exact.front().makespan, "symmetric bracket: fastest bound: " + describe(in));
        for(std::size_t i = 0; i < bracket.gapLower.size() && i + 1 < exact.size(); ++i)
            check(bracket.gapLower[i] <= exact[i].cost, "symmetric bracket: gap bound below the front: " + describe(in));
    }
}

// Non-symmetric instances against the brute-force oracle, which simulates
// every schedule with its waiting: every upper point is achieved, so the true
// front weakly dominates it; the lower bounds never exceed the true front;
// and an exact bracket is the true front.
void testBracketNonSymmetric(std::mt19937& rng, int trials)
{
    int exactCount = 0;
    for(int trial = 0; trial < trials; ++trial)
    {
        zeno::Instance in = randomInstance(rng, 3, 4, 2, 6);
        if(in.t == in.p)
            ++in.t; // the brute-force oracle needs t > p
        std::uniform_int_distribution<int> value(0, 12);
        for(auto& v : in.dbar)
            v = value(rng);
        oracle::Instance o;
        o.travelers = static_cast<unsigned>(in.t);
        o.planes = static_cast<unsigned>(in.p);
        for(int i = 0; i < in.n(); ++i)
        {
            o.cost.push_back(in.c[static_cast<std::size_t>(i)]);
            o.west.push_back(in.d[static_cast<std::size_t>(i)]);
            o.east.push_back(in.dbar[static_cast<std::size_t>(i)]);
        }
        std::vector<zeno::FrontPoint> truth;
        for(const auto& [cost, makespan] : oracle::paretoFront(o))
            truth.push_back({cost, makespan});
        const zeno::Front front = zeno::paretoFilter(truth);
        zeno::SolveOptions options;
        options.plans = true;
        const auto bracket = zeno::solveBracket(in, options);
        const std::string where = describe(in) + " dbar=" + [&] { std::string s; for(auto v : in.dbar) s += std::to_string(v) + ","; return s; }();
        for(const auto& point : bracket.upper)
            check(std::ranges::any_of(front, [&](const zeno::FrontPoint& f) { return f.cost <= point.cost && f.makespan <= point.makespan; }),
                  "non-symmetric upper point is dominated by the true front: " + where);
        for(std::size_t i = 0; i < bracket.plans.size(); ++i)
        {
            const auto ok = zeno::checkPlan(in, bracket.plans[i]);
            check(ok.ok && ok.cost == bracket.upper[i].cost && ok.makespan == bracket.upper[i].makespan, "non-symmetric plan realises its point: " + where);
        }
        check(bracket.fastestLower <= front.front().makespan, "non-symmetric fastest bound: " + where);
        for(std::size_t i = 0; i < bracket.gapLower.size(); ++i)
            for(const auto& f : front)
                if(f.makespan < bracket.upper[i + 1].makespan)
                    check(bracket.gapLower[i] <= f.cost, "non-symmetric gap bound below the true front: " + where);
        if(bracket.exact())
        {
            ++exactCount;
            check(bracket.upper == front, "exact non-symmetric bracket = true front: " + where);
        }
    }
    std::cout << "ut-zeno-core: " << exactCount << " of " << trials << " non-symmetric brackets are exact\n";
}

// The balanced role program and its bounds on random non-symmetric
// instances: the Lagrangian bound never exceeds the balanced optimum, the
// target-pruned search agrees with the full one, and the optimum's
// configuration is balanced, has s landings and fits the level.
void testBalancedRoles(std::mt19937& rng, int trials)
{
    for(int trial = 0; trial < trials; ++trial)
    {
        zeno::Instance in = randomInstance(rng, 4, 6, 3, 9);
        std::uniform_int_distribution<int> value(0, 12);
        for(auto& v : in.dbar)
            v = value(rng);
        const auto r = zeno::reduce(in);
        const zeno::Time hi = r.highestLevel();
        const zeno::OnePlaneTable G(r.fill, r.c, r.maxGroup(), hi);
        for(zeno::Time T = r.lowestLevel(); T <= hi; T += std::max<zeno::Time>(1, (hi - r.lowestLevel()) / 6))
        {
            const zeno::BalancedRoles full(r, G, T);
            if(!full.complete())
                continue;
            const std::string where = describe(in) + " T=" + std::to_string(T);
            const auto lagrange = zeno::lagrangianRoles(r, T, full.value());
            check(lagrange.value <= full.value(), "Lagrangian bound <= balanced optimum: " + where);
            check(zeno::lagrangianValue(r, T, lagrange.multipliers) == lagrange.value, "Lagrangian multipliers reproduce the bound: " + where);
            if(zeno::isInf(full.value()))
                continue;
            for(zeno::Cost target : {full.value(), full.value() + 1, full.value() + 50})
            {
                const zeno::BalancedRoles pruned(r, G, T, 2'000'000, 50'000'000, target);
                check(pruned.complete() && pruned.value() == std::min(full.value(), target), "pruned search agrees: " + where);
            }
            const zeno::RoleConfig config = full.reconstruct();
            std::vector<int> balance(static_cast<std::size_t>(r.n()), 0);
            int landings = 0;
            zeno::Cost cost = 0;
            bool fits = true;
            for(std::size_t k = 0; k < config.drops.size(); ++k)
            {
                zeno::Time load = 0;
                for(int x : config.drops[k]) { ++balance[static_cast<std::size_t>(x)]; load += r.drop[static_cast<std::size_t>(x)]; cost += r.c[static_cast<std::size_t>(x)]; }
                for(int x : config.picks[k]) { --balance[static_cast<std::size_t>(x)]; load += r.pick[static_cast<std::size_t>(x)]; cost += r.c[static_cast<std::size_t>(x)]; }
                for(int x : config.crossings[k]) { load += r.fill[static_cast<std::size_t>(x)]; cost += r.c[static_cast<std::size_t>(x)]; }
                landings += static_cast<int>(config.drops[k].size() + config.picks[k].size() + config.crossings[k].size());
                fits = fits && load <= T && config.crossings[k].size() % 2 == 1;
            }
            check(std::ranges::all_of(balance, [](int b) { return b == 0; }) && landings == r.landings() && fits && cost == full.value(),
                  "balanced configuration is consistent: " + where);
            if(auto plan = zeno::scheduleRoles(in, r, config))
            {
                const auto ok = zeno::checkPlan(in, *plan);
                check(ok.ok && ok.cost == full.value(), "scheduled configuration simulates at its cost: " + where);
            }
        }
    }
}

// Metamorphic properties of the exact front: transformations of the
// instance with a known effect on the front.
void testMetamorphic(std::mt19937& rng, int trials, const Sizes& z)
{
    for(int trial = 0; trial < trials; ++trial)
    {
        const zeno::Instance in = randomInstance(rng, z.n, z.t, z.p, z.s);
        const zeno::Front front = zeno::solveFront(in).front;
        const std::string where = describe(in);
        const auto solve = [](const zeno::Instance& x) { return zeno::solveFront(x).front; };

        // Permuting the cities.
        zeno::Instance permuted = in;
        std::vector<std::size_t> order(static_cast<std::size_t>(in.n()));
        std::iota(order.begin(), order.end(), std::size_t{0});
        std::ranges::shuffle(order, rng);
        for(std::size_t i = 0; i < order.size(); ++i)
        {
            permuted.d[i] = in.d[order[i]];
            permuted.c[i] = in.c[order[i]];
        }
        permuted.dbar = permuted.d;
        check(solve(permuted) == front, "permuting cities keeps the front: " + where);

        // Scaling durations by k scales makespans; scaling costs scales costs.
        const zeno::Cost k = std::uniform_int_distribution<int>(2, 5)(rng);
        zeno::Instance slower = in, dearer = in;
        for(auto& v : slower.d) v *= k;
        slower.dbar = slower.d;
        for(auto& v : dearer.c) v *= k;
        zeno::Front expectSlower = front, expectDearer = front;
        for(auto& point : expectSlower) point.makespan *= k;
        for(auto& point : expectDearer) point.cost *= k;
        check(solve(slower) == expectSlower, "scaling durations scales makespans: " + where);
        check(solve(dearer) == expectDearer, "scaling costs scales costs: " + where);

        // A dominated city and a duplicate city change nothing.
        zeno::Instance extra = in;
        const auto i = std::uniform_int_distribution<std::size_t>(0, static_cast<std::size_t>(in.n() - 1))(rng);
        extra.d.push_back(in.d[i] + std::uniform_int_distribution<int>(0, 3)(rng));
        extra.c.push_back(in.c[i] + std::uniform_int_distribution<int>(0, 3)(rng));
        extra.d.push_back(in.d[i]);
        extra.c.push_back(in.c[i]);
        extra.dbar = extra.d;
        check(solve(extra) == front, "dominated and duplicate cities keep the front: " + where);

        // Adding a to every cost adds s * a to every front cost: front plans
        // land exactly s times.
        const zeno::Cost a = std::uniform_int_distribution<int>(1, 7)(rng);
        zeno::Instance shifted = in;
        for(auto& v : shifted.c) v += a;
        zeno::Front expectShifted = front;
        for(auto& point : expectShifted) point.cost += a * in.landings();
        check(solve(shifted) == expectShifted, "shifting costs shifts the front by s * a: " + where);
    }
}

// Version 2 certificates of exact non-symmetric brackets: they round-trip,
// are accepted, and are rejected once corrupted.
void testBracketCertificates(std::mt19937& rng, int trials)
{
    zeno::SolveOptions options;
    options.plans = true;
    int written = 0;
    for(int trial = 0; trial < trials; ++trial)
    {
        zeno::Instance in = randomInstance(rng, 4, 6, 3, 9);
        std::uniform_int_distribution<int> value(0, 12);
        for(auto& v : in.dbar)
            v = value(rng);
        const auto bracket = zeno::solveBracket(in, options);
        if(!bracket.exact())
            continue;
        ++written;
        const auto cert = zeno::makeBracketCertificate(in, bracket);
        std::stringstream text;
        zeno::writeCertificate(text, cert);
        const auto back = zeno::readCertificate(text);
        const auto report = zeno::checkCertificate(back);
        const std::string where = describe(in);
        check(report.ok, "v2 certificate accepted: " + where + (report.errors.empty() ? "" : ": " + report.errors.front()));
        check(back.version == 2 && back.front == cert.front && back.gaps == cert.gaps && back.multipliers == cert.multipliers,
              "v2 certificate round trip: " + where);
        const auto rejected = [&](const zeno::Certificate& bad, const std::string& what) {
            check(!zeno::checkCertificate(bad).ok, "corrupted v2 certificate rejected (" + what + "): " + where);
        };
        zeno::Certificate bad = cert;
        bad.front.front().makespan -= 1;
        rejected(bad, "fastest point made faster");
        if(cert.front.size() >= 3)
        {
            bad = cert;
            bad.front.erase(bad.front.begin() + 1);
            bad.plans.erase(bad.plans.begin() + 1);
            bad.gaps.erase(bad.gaps.begin() + 1);
            bad.multipliers.erase(bad.multipliers.begin() + 1);
            rejected(bad, "a point removed");
        }
        if(std::ranges::find(cert.assumptions, std::string("A1-NS")) != cert.assumptions.end())
        {
            bad = cert;
            std::erase(bad.assumptions, std::string("A1-NS"));
            rejected(bad, "assumption A1-NS dropped");
        }
    }
    std::cout << "ut-zeno-core: " << written << " non-symmetric certificates checked\n";
}

// Proposition 6.5 of the theory note: harmful waiting. The role-load bound
// stays below the true front in two gaps; the bracket must equal the oracle's
// front and must not claim those gaps closed.
void testHarmfulWaiting()
{
    zeno::Instance in;
    in.d = {3, 19};
    in.dbar = {3, 11};
    in.c = {5, 1};
    in.t = 7;
    in.p = 4;
    oracle::Instance o;
    o.travelers = 7;
    o.planes = 4;
    o.cost = {5, 1};
    o.west = {3, 19};
    o.east = {3, 11};
    std::vector<zeno::FrontPoint> truth;
    for(const auto& [cost, makespan] : oracle::paretoFront(o))
        truth.push_back({cost, makespan});
    const auto bracket = zeno::solveBracket(in);
    check(bracket.upper == zeno::paretoFilter(truth), "harmful waiting: the bracket's points are the true front");
    check(!bracket.exact(), "harmful waiting: the bracket does not claim exactness");
    for(std::size_t i = 0; i < bracket.gapProof.size(); ++i)
        if(bracket.upper[i].makespan == 68)
            check(bracket.gapProof[i] == zeno::GapProof::Open && bracket.gapLower[i] == 14, "harmful waiting: the gap 68-74 is open with bound 14");
}

void testRejects()
{
    zeno::Instance in;
    in.d = {1, 2};
    in.dbar = {1, 3};
    in.c = {2, 1};
    in.t = 3;
    in.p = 2;
    bool threw = false;
    try
    {
        (void)zeno::solveFront(in);
    }
    catch(const std::invalid_argument&)
    {
        threw = true;
    }
    check(threw, "non-symmetric instances are rejected");
    in.dbar = in.d;
    in.p = 4;
    threw = false;
    try
    {
        (void)zeno::solveFront(in);
    }
    catch(const std::invalid_argument&)
    {
        threw = true;
    }
    check(threw, "p > t is rejected");
}
} // namespace

int main(int argc, char** argv)
{
    // ut-zeno-core [trials [maxN maxT maxP maxS]]: random instances per
    // differential test, and their size limits.
    const int trials = argc > 1 ? std::atoi(argv[1]) : 400;
    Sizes sizes;
    if(argc > 5)
        sizes = {std::atoi(argv[2]), std::atoi(argv[3]), std::atoi(argv[4]), std::atoi(argv[5])};
    std::mt19937 rng(20261123);
    testParetoFilter();
    testReduce();
    testOnePlaneTable(rng);
    testLevels(rng, trials, sizes);
    testFront(rng, trials, sizes);
    testPlans(rng, trials, sizes);
    testCertificates(rng, trials, sizes);
    testBracketSymmetric(rng, trials, sizes);
    testBracketNonSymmetric(rng, trials / 4);
    testBalancedRoles(rng, trials / 4);
    testMetamorphic(rng, trials, sizes);
    testBracketCertificates(rng, trials / 4);
    testHarmfulWaiting();
    testRejects();
    if(failures == 0)
        std::cout << "ut-zeno-core: all checks passed\n";
    else
        std::cerr << failures << " checks failed\n";
    return failures == 0 ? 0 : 1;
}
