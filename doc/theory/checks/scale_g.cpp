// Prototype (symmetric durations): exact Pareto front by enumerating landing
// multisets X and solving each exactly with the admissible-partition
// characterisation, plus density statistics and a DP over planes that brackets
// the front without enumerating PPPs.
//
// Usage: scale <mode> <d1,d2,...> <c1,c2,...> <t> <p>
//   front  : print the exact front as "cost makespan" lines
//   stats  : densities (lower bound tight, greedy reaches it, ...), pruning, DP
//   stats0 : same without the paper's greedy (which is the slow part)
//   dp     : DP bracket only (for instances too large to enumerate)
#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <numeric>
#include <string>
#include <vector>

using Int = long long;
const Int INF = (Int)4e18;

struct Inst { std::vector<Int> d, c; int t = 0, p = 0; int n() const { return (int)d.size(); } int s() const { return 2 * t - p; } };

static double now() { return std::chrono::duration<double>(std::chrono::steady_clock::now().time_since_epoch()).count(); }

// ---------------------------------------------------------------- exact M(X)
struct PartitionSearch
{
    const Inst& in; const std::vector<int>& x;
    std::vector<int> jobs, assigned;
    std::vector<std::vector<int>> count; std::vector<Int> load; std::vector<int> size;
    Int best = INF, lb = 0; long nodes = 0;

    PartitionSearch(const Inst& i, const std::vector<int>& X, Int lowerBound) : in(i), x(X),
        count(i.p, std::vector<int>(i.n(), 0)), load(i.p, 0), size(i.p, 0), lb(lowerBound)
    {
        for(int c = 0; c < in.n(); ++c) for(int k = 0; k < x[c]; ++k) jobs.push_back(c);
        std::sort(jobs.begin(), jobs.end(), [&](int a, int b) { return in.d[a] != in.d[b] ? in.d[a] > in.d[b] : a < b; });
        assigned.assign(jobs.size(), 0);
    }
    // Every connected component of the planes x cities graph must hold an even
    // number of planes with an even number of landings.
    bool admissible() const
    {
        const int p = in.p, n = in.n();
        std::vector<int> parent(p + n); std::iota(parent.begin(), parent.end(), 0);
        std::function<int(int)> find = [&](int v) { return parent[v] == v ? v : parent[v] = find(parent[v]); };
        for(int k = 0; k < p; ++k) for(int c = 0; c < n; ++c) if(count[k][c] > 0) parent[find(k)] = find(p + c);
        std::vector<int> even(p + n, 0);
        for(int k = 0; k < p; ++k) if(size[k] % 2 == 0) ++even[find(k)];
        for(int v : even) if(v % 2) return false;
        return true;
    }
    void rec(std::size_t j, int used)
    {
        ++nodes;
        if(best == lb) return;
        if(j == jobs.size())
        {
            if(used == in.p && admissible()) best = std::min(best, *std::max_element(load.begin(), load.end()));
            return;
        }
        if((int)(jobs.size() - j) < in.p - used) return;
        // Identical landings go to planes in non-decreasing order; planes are
        // numbered by first use (they are interchangeable).
        const int from = (j > 0 && jobs[j] == jobs[j - 1]) ? assigned[j - 1] : 0;
        const Int w = 2 * in.d[jobs[j]];
        for(int k = from; k < std::min(used + 1, in.p); ++k)
        {
            if(load[k] + w >= best) continue;
            load[k] += w; ++size[k]; ++count[k][jobs[j]]; assigned[j] = k;
            rec(j + 1, std::max(used, k + 1));
            load[k] -= w; --size[k]; --count[k][jobs[j]];
            if(best == lb) return;
        }
    }
    Int run() { rec(0, 0); return best; }
};

static Int lowerBound(const Inst& in, const std::vector<int>& x)
{
    Int sum = 0, dmax = 0;
    for(int c = 0; c < in.n(); ++c) if(x[c]) { sum += x[c] * in.d[c]; dmax = std::max(dmax, in.d[c]); }
    return std::max<Int>(2 * ((sum + in.p - 1) / in.p), 2 * dmax);
}

// ------------------------------------------------- the paper's two-step greedy
template<class F> static void subsOfSize(const std::vector<int>& bound, int k, F f)
{
    std::vector<int> c(bound.size(), 0);
    std::function<void(std::size_t, int)> rec = [&](std::size_t i, int left)
    {
        if(i == bound.size()) { if(left == 0) f(c); return; }
        for(int v = 0; v <= std::min(bound[i], left); ++v) { c[i] = v; rec(i + 1, left - v); }
        c[i] = 0;
    };
    rec(0, k);
}
template<class F> static void subMultisets(const std::vector<int>& bound, F f)
{
    std::vector<int> c(bound.size(), 0);
    std::function<void(std::size_t)> rec = [&](std::size_t i)
    {
        if(i == bound.size()) { f(c); return; }
        for(int v = 0; v <= bound[i]; ++v) { c[i] = v; rec(i + 1); }
        c[i] = 0;
    };
    rec(0);
}
static Int twoStep(const Inst& in, const std::vector<int>& e, const std::vector<int>& w, const std::vector<int>& beta)
{
    std::vector<Int> ee, ww, bb;
    for(int i = 0; i < in.n(); ++i)
    {
        for(int k = 0; k < e[i] - beta[i]; ++k) ee.push_back(in.d[i]);
        for(int k = 0; k < w[i] - beta[i]; ++k) ww.push_back(in.d[i]);
        for(int k = 0; k < beta[i]; ++k) bb.push_back(in.d[i]);
    }
    auto desc = [](Int a, Int b) { return a > b; };
    std::sort(ee.begin(), ee.end(), desc); std::sort(ww.begin(), ww.end(), desc); std::sort(bb.begin(), bb.end(), desc);
    const int p = in.p; std::vector<Int> D(p, 0); std::vector<char> east(p, 1); std::size_t i = 0, j = 0;
    while(j < ww.size())
    {
        int k = (int)(std::min_element(D.begin(), D.end()) - D.begin());
        if(east[k]) { D[k] += 2 * ee[i++]; east[k] = 0; } else { D[k] += 2 * ww[j++]; east[k] = 1; }
    }
    while(i < ee.size())
    {
        int k = -1; for(int q = 0; q < p; ++q) if(east[q] && (k < 0 || D[q] < D[k])) k = q;
        D[k] += 2 * ee[i++]; east[k] = 0;
    }
    for(Int b : bb)
    {
        if(p == 1) { D[0] += 4 * b; continue; }
        int f = 0; for(int q = 1; q < p; ++q) if(D[q] < D[f]) f = q;
        int g = f == 0 ? 1 : 0; for(int q = 0; q < p; ++q) if(q != f && D[q] < D[g]) g = q;
        D[f] += 2 * b; D[g] += 2 * b;
    }
    return *std::max_element(D.begin(), D.end());
}
static Int paperGreedy(const Inst& in, const std::vector<int>& x)
{
    Int best = INF;
    subsOfSize(x, in.t, [&](const std::vector<int>& e)
    {
        std::vector<int> w(x), common(x.size());
        for(std::size_t i = 0; i < w.size(); ++i) { w[i] -= e[i]; common[i] = std::min(e[i], w[i]); }
        subMultisets(common, [&](const std::vector<int>& beta) { best = std::min(best, twoStep(in, e, w, beta)); });
    });
    return best;
}

// ------------------------------------------------------------ DP over planes
// G[m][T] = cheapest multiset of m landings whose durations sum to at most T
// (a plane with these landings has load 2T). For a makespan bound 2T:
//   lower: planes are independent, any sizes summing to 2t-p (admissibility
//          ignored)                                  -> cost <= exact cost;
//   upper: planes with an even number of landings come in pairs that share a
//          city (always admissible)                  -> cost >= exact cost.
struct DpResult { std::map<Int, Int> lower, upper; double seconds = 0; };
static DpResult dp(const Inst& in)
{
    const double t0 = now();
    const int s = in.s(), p = in.p, n = in.n();
    const int mmax = s - (p - 1);
    const Int dmax = *std::max_element(in.d.begin(), in.d.end());
    const int Tmax = (int)(dmax * mmax);
    std::vector<std::vector<Int>> G(mmax + 1, std::vector<Int>(Tmax + 1, INF));
    for(int T = 0; T <= Tmax; ++T) G[0][T] = 0;
    for(int m = 1; m <= mmax; ++m)
        for(int T = 0; T <= Tmax; ++T)
            for(int i = 0; i < n; ++i)
                if(T >= in.d[i] && G[m - 1][T - in.d[i]] < INF)
                    G[m][T] = std::min(G[m][T], in.c[i] + G[m - 1][T - in.d[i]]);

    DpResult r; Int bestL = INF, bestU = INF;
    std::vector<std::vector<Int>> L(p + 1, std::vector<Int>(s + 1)), U(p + 1, std::vector<Int>(s + 1));
    std::vector<std::vector<Int>> H(mmax + 1, std::vector<Int>(mmax + 1));
    std::vector<Int> A(mmax + 1);
    for(int T = 0; T <= Tmax; ++T)
    {
        for(auto& row : L) std::fill(row.begin(), row.end(), INF);
        for(auto& row : U) std::fill(row.begin(), row.end(), INF);
        L[0][0] = U[0][0] = 0;
        // Pairs of even planes sharing city i.
        for(auto& row : H) std::fill(row.begin(), row.end(), INF);
        for(int i = 0; i < n; ++i)
        {
            if(T < in.d[i]) continue;
            for(int m = 2; m <= mmax; m += 2) A[m] = G[m - 1][T - in.d[i]] < INF ? in.c[i] + G[m - 1][T - in.d[i]] : INF;
            for(int a = 2; a <= mmax; a += 2) if(A[a] < INF)
                for(int b = a; b <= mmax; b += 2) if(A[b] < INF)
                    H[a][b] = std::min(H[a][b], A[a] + A[b]);
        }
        for(int k = 1; k <= p; ++k)
            for(int j = k; j <= s; ++j)
            {
                Int vl = INF, vu = INF;
                for(int m = 1; m <= std::min(mmax, j - (k - 1)); ++m)
                {
                    if(G[m][T] >= INF) continue;
                    if(L[k - 1][j - m] < INF) vl = std::min(vl, L[k - 1][j - m] + G[m][T]);
                    if((m & 1) && U[k - 1][j - m] < INF) vu = std::min(vu, U[k - 1][j - m] + G[m][T]);
                }
                if(k >= 2)
                    for(int a = 2; a <= mmax; a += 2)
                        for(int b = a; b <= mmax && a + b <= j - (k - 2); b += 2)
                            if(H[a][b] < INF && U[k - 2][j - a - b] < INF)
                                vu = std::min(vu, U[k - 2][j - a - b] + H[a][b]);
                L[k][j] = vl; U[k][j] = vu;
            }
        if(L[p][s] < bestL) { bestL = L[p][s]; r.lower[bestL] = 2 * T; }
        if(U[p][s] < bestU) { bestU = U[p][s]; r.upper[bestU] = 2 * T; }
    }
    r.seconds = now() - t0;
    return r;
}

// --------------------------------------------------------------------- main
static std::vector<Int> parseList(const std::string& s)
{
    std::vector<Int> v; std::size_t pos = 0;
    while(pos < s.size()) { std::size_t q = s.find(',', pos); if(q == std::string::npos) q = s.size(); v.push_back(std::atoll(s.substr(pos, q - pos).c_str())); pos = q + 1; }
    return v;
}
static std::map<Int, Int> pareto(const std::map<Int, Int>& perCost)
{
    std::map<Int, Int> f; Int best = INF;
    for(auto& kv : perCost) if(kv.second < best) { f[kv.first] = kv.second; best = kv.second; }
    return f;
}

int main(int argc, char** argv)
{
    if(argc < 6) { std::fprintf(stderr, "usage: scale <front|stats|stats0|dp> d c t p\n"); return 2; }
    const std::string mode = argv[1];
    Inst in; in.d = parseList(argv[2]); in.c = parseList(argv[3]); in.t = std::atoi(argv[4]); in.p = std::atoi(argv[5]);
    const int n = in.n(), s = in.s();

    if(mode == "dp")
    {
        auto r = dp(in);
        std::printf("dp: lower front %zu points, upper front %zu points, identical: %s, %.3f s\n",
            r.lower.size(), r.upper.size(), r.lower == r.upper ? "yes" : "NO", r.seconds);
        if(r.lower != r.upper)
        {
            // Compare as staircases: for each makespan of either front, the cheapest cost reachable.
            auto costAt = [](const std::map<Int, Int>& f, Int makespan) { Int best = INF; for(auto& kv : f) if(kv.second <= makespan) best = std::min(best, kv.first); return best; };
            std::map<Int, int> makespans; for(auto& kv : r.lower) makespans[kv.second] = 1; for(auto& kv : r.upper) makespans[kv.second] = 1;
            int differ = 0; double worst = 0;
            for(auto& kv : makespans)
            {
                const Int l = costAt(r.lower, kv.first), u = costAt(r.upper, kv.first);
                if(l != u) { ++differ; if(l < INF && u < INF) worst = std::max(worst, (double)(u - l) / (double)l); }
            }
            std::printf("    makespan levels where the bounds differ: %d of %zu, largest cost gap %.3f%%\n", differ, makespans.size(), 100 * worst);
        }
        return 0;
    }

    const bool withGreedy = mode == "stats" || mode == "gfront";
    std::map<Int, Int> perCostG;
    const bool keepRows = mode != "exact" && mode != "front" && mode != "gfront";
    long countX = 0, totalNodes = 0, tightCount = 0;
    struct Row { Int cost, lb, m, g; long nodes; };
    std::vector<Row> rows; std::map<Int, Int> perCost;
    std::vector<int> x(n, 0);
    const Int witnessCost = std::getenv("WITNESS_COST") ? std::atoll(std::getenv("WITNESS_COST")) : -1;
    const double t0 = now(); double greedySeconds = 0;
    std::function<void(int, int)> rec = [&](int city, int left)
    {
        if(city == n - 1)
        {
            x[city] = left;
            Row row; row.cost = 0; for(int i = 0; i < n; ++i) row.cost += x[i] * in.c[i];
            row.lb = lowerBound(in, x);
            PartitionSearch ps(in, x, row.lb); row.m = ps.run(); row.nodes = ps.nodes;
            row.g = 0;
            if(withGreedy) { const double g0 = now(); row.g = paperGreedy(in, x); greedySeconds += now() - g0; }
            ++countX; totalNodes += row.nodes; if(row.m == row.lb) ++tightCount;
            if(keepRows) rows.push_back(row);
            if(witnessCost >= 0 && row.cost == witnessCost)
            {
                std::printf("W cost %lld makespan %lld lb %lld x=", row.cost, row.m, row.lb);
                for(int i = 0; i < n; ++i) std::printf("%d%s", x[i], i + 1 < n ? "," : "\n");
            }
            if(withGreedy) { auto g = perCostG.find(row.cost); if(g == perCostG.end() || row.g < g->second) perCostG[row.cost] = row.g; }
            auto it = perCost.find(row.cost);
            if(it == perCost.end() || row.m < it->second) perCost[row.cost] = row.m;
            x[city] = 0; return;
        }
        for(int v = left; v >= 0; --v) { x[city] = v; rec(city + 1, left - v); }
        x[city] = 0;
    };
    rec(0, s);
    const double exactSeconds = now() - t0 - greedySeconds;
    const auto front = pareto(perCost);

    if(mode == "support")
    {
        // Second pass: for each cost on the front, find the minimal support among multisets reaching the front makespan.
        std::map<Int, int> minSupport;
        std::vector<int> y(n, 0);
        std::function<void(int, int)> rec2 = [&](int city, int left)
        {
            if(city == n - 1)
            {
                y[city] = left;
                Int cost = 0; int support = 0; for(int i = 0; i < n; ++i) { cost += y[i] * in.c[i]; if(y[i]) ++support; }
                auto it = front.find(cost);
                if(it != front.end())
                {
                    PartitionSearch ps(in, y, lowerBound(in, y));
                    if(ps.run() == it->second) { auto jt = minSupport.find(cost); if(jt == minSupport.end() || support < jt->second) minSupport[cost] = support; }
                }
                y[city] = 0; return;
            }
            for(int v = left; v >= 0; --v) { y[city] = v; rec2(city + 1, left - v); }
            y[city] = 0;
        };
        rec2(0, s);
        std::map<int, int> hist; for(auto& kv : minSupport) ++hist[kv.second];
        std::printf("front %zu points; distinct cities needed:", front.size());
        for(auto& kv : hist) std::printf("  %d city%s: %d", kv.first, kv.first > 1 ? "s" : "", kv.second);
        std::printf("\n");
        return 0;
    }
    if(mode == "gfront") { for(auto& kv : pareto(perCostG)) std::printf("%lld %lld\n", kv.first, kv.second); return 0; }
    if(mode == "front") { for(auto& kv : front) std::printf("%lld %lld\n", kv.first, kv.second); return 0; }
    if(mode == "exact")
    {
        auto r = dp(in);
        std::printf("multisets X: %ld   exact front: %zu points   exact enumeration: %.2f s (%.0f nodes per X)   LB tight: %.1f%%\n",
            countX, front.size(), exactSeconds, (double)totalNodes / countX, 100.0 * tightCount / countX);
        std::printf("dp: lower %zu points, upper %zu points, lower==upper: %s, upper==exact: %s, lower==exact: %s, %.3f s\n",
            r.lower.size(), r.upper.size(), r.lower == r.upper ? "yes" : "NO", r.upper == front ? "yes" : "NO",
            r.lower == front ? "yes" : "NO", r.seconds);
        if(std::getenv("PRINT_FRONT")) for(auto& kv : front) std::printf("F %lld %lld\n", kv.first, kv.second);
        return 0;
    }

    // Staircase: best makespan among front points with cost <= C.
    auto stair = [&](Int cost) { auto it = front.upper_bound(cost); if(it == front.begin()) return INF; --it; return it->second; };
    long tight = 0, gLb = 0, gOpt = 0, essential = 0, essentialNeedSearch = 0, nodes = 0, onFront = 0;
    for(auto& r : rows)
    {
        nodes += r.nodes;
        if(r.m == r.lb) ++tight;
        if(withGreedy) { if(r.g == r.lb) ++gLb; if(r.g == r.m) ++gOpt; }
        const Int f = stair(r.cost);
        if(r.lb < f || (r.lb == f && front.count(r.cost) && front.at(r.cost) == r.m && r.m == f)) { /* counted below */ }
        if(r.lb < f) { ++essential; if(withGreedy && r.g > r.lb) ++essentialNeedSearch; }
        if(front.count(r.cost) && front.at(r.cost) == r.m) ++onFront;
    }
    const double N = (double)rows.size();
    std::printf("multisets X: %zu   front: %zu points   exact enumeration: %.2f s (%.0f search nodes per X)\n",
        rows.size(), front.size(), exactSeconds, nodes / N);
    std::printf("lower bound tight (M = LB): %.1f%%\n", 100 * tight / N);
    if(withGreedy)
        std::printf("greedy reaches LB: %.1f%%   greedy optimal: %.1f%%   (greedy time %.1f s)\n", 100 * gLb / N, 100 * gOpt / N, greedySeconds);
    std::printf("X whose LB is below the final front (cannot be pruned by the bound): %ld (%.2f%%)\n", essential, 100 * essential / N);
    if(withGreedy)
        std::printf("  of those, greedy does not reach LB (need exact search): %ld (%.2f%%)\n", essentialNeedSearch, 100 * essentialNeedSearch / N);
    auto r = dp(in);
    if(std::getenv("SHOW_DIFF"))
    {
        std::map<Int, int> keys;
        for(auto& kv : front) keys[kv.first] |= 1;
        for(auto& kv : r.lower) keys[kv.first] |= 2;
        for(auto& kv : r.upper) keys[kv.first] |= 4;
        int shown = 0;
        for(auto& kv : keys)
        {
            const Int c = kv.first;
            const Int e = front.count(c) ? front.at(c) : -1, l = r.lower.count(c) ? r.lower.at(c) : -1, u = r.upper.count(c) ? r.upper.at(c) : -1;
            if(e == l && e == u) continue;
            if(shown++ < 12) std::printf("  cost %lld: exact %lld  lower %lld  upper %lld\n", c, e, l, u);
        }
        std::printf("  (%d costs differ; -1 = no point at that cost)\n", shown);
    }
    std::printf("dp: lower %zu points, upper %zu points, lower==upper: %s, upper==exact: %s, lower==exact: %s, %.3f s\n",
        r.lower.size(), r.upper.size(), r.lower == r.upper ? "yes" : "NO", r.upper == front ? "yes" : "NO",
        r.lower == front ? "yes" : "NO", r.seconds);
    return 0;
}
