// The per-PPP greedy of Quemy & Schoenauer (EvoCOP 2015, Algorithm 1), reimplemented from the 2016
// `zenoSolver` (commit 84ca92a, src/solver.cpp and symetric::UpperBound in src/algorithm.cpp) for
// symmetric instances. It shares no code with the exact solver.
//
// For every PPP, a t-multiset e of eastward crossings and a (t-p)-multiset w of westward ones, and
// every sub-multiset beta of their common part (the P3 patterns), the greedy deals the remaining
// crossings longest first to the least-loaded plane, alternating east and west per plane, then gives
// the leftover east crossings to planes that still need one, then each P3 to the two least-loaded
// planes. The PPP's makespan is the best over beta; the greedy front is the Pareto set of
// (cost of e + w, makespan) over all PPPs.
//
// usage: greedy <d1,d2,...> <c1,c2,...> <t> <p> [noprune]
// Prints the greedy front as "cost makespan" lines by increasing cost, and on stderr the number of
// PPPs and of PPPs evaluated. By default a PPP whose load bound is already weakly dominated by a found
// point is skipped (the 2016 `-a` pruning): this cannot change the Pareto set.
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <map>
#include <numeric>
#include <string>
#include <vector>

using Int = long long;

static std::vector<Int> parseList(const char* s)
{
    std::vector<Int> v;
    std::string str(s);
    std::size_t pos = 0;
    while(pos <= str.size())
    {
        std::size_t q = str.find(',', pos);
        if(q == std::string::npos) q = str.size();
        if(q > pos) v.push_back(std::atoll(str.substr(pos, q - pos).c_str()));
        pos = q + 1;
    }
    return v;
}

// Next non-decreasing k-tuple over [0, n) (the 2016 nextTuple); false when done.
static bool nextTuple(std::vector<int>& v, int n)
{
    const int k = (int)v.size();
    if(k == 0) return false;
    if(v[k - 1] < n - 1) { ++v[k - 1]; return true; }
    int j = k - 2;
    while(j >= 0 && v[j] == n - 1) --j;
    if(j < 0) return false;
    ++v[j];
    for(int i = j + 1; i < k; ++i) v[i] = v[j];
    return true;
}

struct Greedy
{
    int n, t, p;
    std::vector<Int> w2;  // weight of a crossing through city i: d_i + dbar_i = 2 d_i
    std::vector<Int> m;
    std::vector<char> east;
    std::vector<int> alphaE, alphaW;

    // Makespan of the greedy for one beta (counts per city); e, w as sorted city tuples.
    Int run(const std::vector<int>& e, const std::vector<int>& w, const std::vector<int>& beta)
    {
        // alpha = multiset difference, iterated from the end (largest city index, i.e. longest).
        std::vector<int> left(beta);
        alphaE.clear();
        for(int k = (int)e.size() - 1; k >= 0; --k)
        {
            if(left[e[k]] > 0) { --left[e[k]]; continue; }
            alphaE.push_back(e[k]);
        }
        left = beta;
        alphaW.clear();
        for(int k = (int)w.size() - 1; k >= 0; --k)
        {
            if(left[w[k]] > 0) { --left[w[k]]; continue; }
            alphaW.push_back(w[k]);
        }
        std::fill(m.begin(), m.end(), 0);
        std::fill(east.begin(), east.end(), 1);
        std::size_t iE = 0, iW = 0;
        while(iW < alphaW.size())
        {
            int k = (int)(std::min_element(m.begin(), m.end()) - m.begin());
            if(east[k]) { m[k] += w2[alphaE[iE++]]; east[k] = 0; }
            else { m[k] += w2[alphaW[iW++]]; east[k] = 1; }
        }
        while(iE < alphaE.size())
        {
            // compMS: planes heading east first, then by load; the first minimal one.
            int k = -1;
            for(int q = 0; q < p; ++q)
                if(k < 0 || (east[q] && !east[k]) || (east[q] == east[k] && m[q] < m[k])) k = q;
            m[k] += w2[alphaE[iE++]];
            east[k] = 0;
        }
        // Pattern 3, in increasing city order: both halves to the two least-loaded planes.
        for(int i = 0; i < n; ++i)
            for(int r = 0; r < beta[i]; ++r)
            {
                if(p == 1) { m[0] += 2 * w2[i]; continue; }
                int f = 0;
                for(int q = 1; q < p; ++q) if(m[q] < m[f]) f = q;
                int g = f == 0 ? 1 : 0;
                for(int q = 0; q < p; ++q) if(q != f && m[q] < m[g]) g = q;
                m[f] += w2[i];
                m[g] += w2[i];
            }
        return *std::max_element(m.begin(), m.end());
    }
};

int main(int argc, char** argv)
{
    if(argc < 5) { std::fprintf(stderr, "usage: greedy d1,d2,... c1,c2,... t p [noprune]\n"); return 2; }
    std::vector<Int> d = parseList(argv[1]), c = parseList(argv[2]);
    const int t = std::atoi(argv[3]), p = std::atoi(argv[4]);
    const bool prune = !(argc > 5 && std::strcmp(argv[5], "noprune") == 0);
    if(d.size() != c.size() || d.empty() || p < 1 || p > t) { std::fprintf(stderr, "bad instance\n"); return 2; }
    const int n = (int)d.size();
    // Cities in increasing duration, as the 2016 solver assumed (its generators produce them so).
    std::vector<int> order(n);
    std::iota(order.begin(), order.end(), 0);
    std::stable_sort(order.begin(), order.end(), [&](int a, int b) { return d[a] != d[b] ? d[a] < d[b] : c[a] < c[b]; });
    std::vector<Int> ds(n), cs(n);
    for(int i = 0; i < n; ++i) { ds[i] = d[order[i]]; cs[i] = c[order[i]]; }

    Greedy g{n, t, p, std::vector<Int>(n), std::vector<Int>(p), std::vector<char>(p), {}, {}};
    for(int i = 0; i < n; ++i) g.w2[i] = 2 * ds[i];

    std::map<Int, Int> stair;  // Pareto staircase found so far: cost -> makespan
    auto dominatedBy = [&](Int cost, Int makespan)
    {
        auto it = stair.upper_bound(cost);
        if(it == stair.begin()) return false;
        --it;
        return it->second <= makespan;
    };
    auto insert = [&](Int cost, Int makespan)
    {
        if(dominatedBy(cost, makespan)) return;
        auto it = stair.lower_bound(cost);
        while(it != stair.end() && it->second >= makespan) it = stair.erase(it);
        stair[cost] = makespan;
    };

    long long ppps = 0, evaluated = 0;
    std::vector<int> e(t, 0);
    std::vector<int> ec(n), wc(n), common(n), beta(n);
    do
    {
        std::vector<int> w(t - p, 0);
        do
        {
            ++ppps;
            std::fill(ec.begin(), ec.end(), 0);
            std::fill(wc.begin(), wc.end(), 0);
            Int C = 0, Mc = 0, big = 0;
            for(int i : e) { ++ec[i]; C += cs[i]; Mc += g.w2[i]; big = std::max(big, g.w2[i]); }
            for(int i : w) { ++wc[i]; C += cs[i]; Mc += g.w2[i]; big = std::max(big, g.w2[i]); }
            const Int Ml = std::max(Mc / p, big);
            if(prune && dominatedBy(C, Ml)) continue;
            ++evaluated;
            for(int i = 0; i < n; ++i) common[i] = std::min(ec[i], wc[i]);
            // Every sub-multiset beta of the common part (betaMax = 100 in 2016: all of them).
            Int best = Mc;
            std::fill(beta.begin(), beta.end(), 0);
            while(true)
            {
                best = std::min(best, g.run(e, w, beta));
                if(best == Ml) break;
                int i = 0;
                while(i < n && beta[i] == common[i]) { beta[i] = 0; ++i; }
                if(i == n) break;
                ++beta[i];
            }
            insert(C, best);
        } while(nextTuple(w, n));
    } while(nextTuple(e, n));

    for(auto& kv : stair) std::printf("%lld %lld\n", kv.first, kv.second);
    std::fprintf(stderr, "ppps %lld evaluated %lld\n", ppps, evaluated);
    return 0;
}
