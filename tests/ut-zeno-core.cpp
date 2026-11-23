// Unit and differential tests of the exact solver (library zeno_core).
//
// The reference is the enumeration oracle (tests/oracle/partitionEnum.hpp),
// which shares no code with the library: every landing multiset, every
// admissible partition.
#include <zeno/forest.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/reduce.hpp>
#include <zeno/solve.hpp>

#include "oracle/partitionEnum.hpp"

#include <algorithm>
#include <cstdlib>
#include <functional>
#include <iostream>
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
        const zeno::OnePlaneTable G(d, c, M, maxT);
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
        std::vector<std::pair<zeno::Cost, zeno::Time>> got;
        for(auto it = single.rbegin(); it != single.rend(); ++it)
            got.emplace_back(it->cost, it->makespan);
        check(got == expected, "solveFront = oracle front: " + describe(in));
        check(single == multi, "solveFront does not depend on the thread count: " + describe(in));
    }
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
    testRejects();
    if(failures == 0)
        std::cout << "ut-zeno-core: all checks passed\n";
    else
        std::cerr << failures << " checks failed\n";
    return failures == 0 ? 0 : 1;
}
