// Search for counterexamples to Conjecture 6.5 (no harmful waiting) of
// doc/theory/exact-front.md: a balanced role configuration whose every
// schedule (drop-offs first, crossings, pick-ups last, any orders of the
// drop-offs and of the pick-ups on each plane, any matching of drop-offs to
// pick-ups in each city) has makespan above max_k lambda_k, under the path
// triangle inequality (dbar_i <= d_i + d_z + dbar_z).
//
// Lemma 6.3 makes the template schedule (drops first, picks last) optimal for
// fixed orders and matching, so the search over orders and matchings is
// exhaustive over schedules.
//
// Usage: waiting_search <trials> <seed> [maxPlanes maxLinks maxDuration tight]
// Prints each counterexample found and a summary line.
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <numeric>
#include <random>
#include <vector>

struct Config
{
    int p = 0, n = 0;
    std::vector<int> d, db;                       // per city
    std::vector<std::vector<int>> drops, picks;   // per plane: cities
    std::vector<int> crossing;                    // per plane: total crossing duration (odd count, folded)
};

static int lambda(const Config& c, int k)
{
    int l = c.crossing[k];
    for(int x : c.drops[k]) l += 2 * c.d[x];
    for(int y : c.picks[k]) l += 2 * c.db[y];
    return l;
}

// Makespan of the template schedule for given orders (the vectors' order) and
// matching match[k][l] = (plane, index) of the drop-off whose passenger pick-up
// l of plane k collects.
static int makespan(const Config& c, const std::vector<std::vector<std::pair<int, int>>>& match)
{
    std::vector<std::vector<int>> avail(c.p);
    for(int k = 0; k < c.p; ++k)
    {
        int now = 0;
        for(int x : c.drops[k]) { avail[k].push_back(now + c.d[x]); now += 2 * c.d[x]; }
    }
    int m = 0;
    for(int k = 0; k < c.p; ++k)
    {
        int now = 0;
        for(int x : c.drops[k]) now += 2 * c.d[x];
        now += c.crossing[k];
        for(std::size_t l = 0; l < c.picks[k].size(); ++l)
        {
            const int y = c.picks[k][l];
            const auto [u, j] = match[k][l];
            now = std::max(now + c.db[y], avail[u][j]) + c.db[y];
        }
        m = std::max(m, now);
    }
    return m;
}

int main(int argc, char** argv)
{
    const long trials = argc > 1 ? std::atol(argv[1]) : 10000;
    std::mt19937 rng(argc > 2 ? std::atoi(argv[2]) : 1);
    const int maxPlanes = argc > 3 ? std::atoi(argv[3]) : 4, maxLinks = argc > 4 ? std::atoi(argv[4]) : 4, maxD = argc > 5 ? std::atoi(argv[5]) : 12;
    const bool tight = argc > 6 && std::atoi(argv[6]) != 0; // one shortest crossing per plane
    long tested = 0, harmful = 0, multiBoth = 0;
    for(long trial = 0; trial < trials; ++trial)
    {
        Config c;
        c.p = std::uniform_int_distribution<int>(2, maxPlanes)(rng);
        c.n = std::uniform_int_distribution<int>(1, 4)(rng);
        std::uniform_int_distribution<int> dur(1, maxD);
        for(int i = 0; i < c.n; ++i) { c.d.push_back(dur(rng)); c.db.push_back(dur(rng)); }
        // Path triangle inequality: dbar_i <= d_i + d_z + dbar_z for all i, z.
        bool ok = true;
        for(int i = 0; i < c.n; ++i)
            for(int z = 0; z < c.n; ++z)
                ok = ok && c.db[i] <= c.d[i] + c.d[z] + c.db[z];
        if(!ok) continue;
        c.drops.assign(c.p, {});
        c.picks.assign(c.p, {});
        const int links = std::uniform_int_distribution<int>(2, maxLinks)(rng);
        for(int e = 0; e < links; ++e)
        {
            const int u = std::uniform_int_distribution<int>(0, c.p - 1)(rng);
            int v = std::uniform_int_distribution<int>(0, c.p - 2)(rng);
            if(v >= u) ++v;
            const int x = std::uniform_int_distribution<int>(0, c.n - 1)(rng);
            c.drops[u].push_back(x);
            c.picks[v].push_back(x);
        }
        bool manyPicks = false, manyDrops = false;
        for(int k = 0; k < c.p; ++k)
        {
            manyPicks = manyPicks || c.picks[k].size() >= 2;
            manyDrops = manyDrops || c.drops[k].size() >= 2;
        }
        // The conjecture is only open when some plane picks up twice and some
        // plane drops off twice (W1 and its time reversal cover the rest).
        if(!(manyPicks && manyDrops)) continue;
        ++multiBoth;
        c.crossing.resize(c.p);
        for(int k = 0; k < c.p; ++k)
        {
            // Short crossing phases make pick-ups start early, where waiting bites.
            const int count = tight ? 1 : 1 + 2 * std::uniform_int_distribution<int>(0, 1)(rng);
            int total = 0;
            for(int r = 0; r < count; ++r)
            {
                int x = std::uniform_int_distribution<int>(0, c.n - 1)(rng);
                if(tight)
                    for(int i = 0; i < c.n; ++i)
                        if(c.d[i] + c.db[i] < c.d[x] + c.db[x]) x = i;
                total += c.d[x] + c.db[x];
            }
            c.crossing[k] = total;
        }
        int Lambda = 0;
        for(int k = 0; k < c.p; ++k) Lambda = std::max(Lambda, lambda(c, k));

        // Exhaustive: orders of drops and picks on every plane, matchings per city.
        int best = 1 << 30;
        std::vector<std::vector<std::pair<int, int>>> match(c.p);
        std::function<void(int)> orderPlane;
        std::function<void()> matchAll = [&] {
            // Pick-ups per city in a fixed global order, drop-offs per city:
            // enumerate bijections city by city.
            std::map<int, std::vector<std::pair<int, int>>> dropsAt, picksAt;
            for(int k = 0; k < c.p; ++k)
            {
                for(int j = 0; j < (int)c.drops[k].size(); ++j) dropsAt[c.drops[k][j]].push_back({k, j});
                for(int l = 0; l < (int)c.picks[k].size(); ++l) picksAt[c.picks[k][l]].push_back({k, l});
            }
            std::vector<int> cities;
            for(auto& [x, v] : picksAt) cities.push_back(x);
            std::function<void(std::size_t)> rec = [&](std::size_t ci) {
                if(ci == cities.size())
                {
                    best = std::min(best, makespan(c, match));
                    return;
                }
                auto ds = dropsAt[cities[ci]];
                const auto& ps = picksAt[cities[ci]];
                std::sort(ds.begin(), ds.end());
                do
                {
                    for(std::size_t q = 0; q < ps.size(); ++q)
                        match[ps[q].first][ps[q].second] = ds[q];
                    rec(ci + 1);
                } while(std::next_permutation(ds.begin(), ds.end()) && best > Lambda);
            };
            for(int k = 0; k < c.p; ++k) match[k].assign(c.picks[k].size(), {0, 0});
            rec(0);
        };
        orderPlane = [&](int k) {
            if(best <= Lambda) return;
            if(k == c.p) { matchAll(); return; }
            std::sort(c.drops[k].begin(), c.drops[k].end());
            do
            {
                std::sort(c.picks[k].begin(), c.picks[k].end());
                do orderPlane(k + 1);
                while(best > Lambda && std::next_permutation(c.picks[k].begin(), c.picks[k].end()));
            } while(best > Lambda && std::next_permutation(c.drops[k].begin(), c.drops[k].end()));
        };
        orderPlane(0);
        ++tested;
        if(best > Lambda)
        {
            ++harmful;
            if(harmful <= 10)
            {
                std::printf("counterexample: max lambda %d, best makespan %d\n  d=", Lambda, best);
                for(int i = 0; i < c.n; ++i) std::printf("%d,", c.d[i]);
                std::printf(" dbar=");
                for(int i = 0; i < c.n; ++i) std::printf("%d,", c.db[i]);
                std::printf("\n");
                for(int k = 0; k < c.p; ++k)
                {
                    std::printf("  plane %d: drops", k);
                    for(int x : c.drops[k]) std::printf(" %d", x);
                    std::printf("; picks");
                    for(int y : c.picks[k]) std::printf(" %d", y);
                    std::printf("; crossings %d; lambda %d\n", c.crossing[k], lambda(c, k));
                }
            }
        }
    }
    std::printf("%ld configurations with a plane picking twice and one dropping twice; %ld tested; %ld with harmful waiting\n", multiBoth, tested, harmful);
    return 0;
}
