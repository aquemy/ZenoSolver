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


// ============ Link-forest tree DP (prototype) ============
// A partition is admissible iff the planes carry a forest whose edges are labelled by cities,
// each edge using one copy of its city in both end planes, and |X_u| - deg(u) is odd for all u.
// So a plane = its edge copies + an odd filler multiset R_u (|R_u| >= 1).
// E(T) = cheapest landing multiset of size s with such a structure and every group duration <= T.
static Int treeDP(const Inst& in, const std::vector<std::vector<Int>>& G, int T)
{
    const int p = in.p, s = in.s(), n = in.n();
    auto inf = [](Int v) { return v >= INF; };
    // K[tau][q][j]: children multiset of a plane: total child-edge durations tau (at the parent side),
    // q planes in the child subtrees, j landings (one copy per child edge at the parent + subtree landings).
    std::vector<std::vector<std::vector<Int>>> K(T + 1, std::vector<std::vector<Int>>(p, std::vector<Int>(s + 1, INF)));
    // S[a][q][j]: subtree hanging from a parent edge labelled a (root holds one copy of a).
    std::vector<std::vector<std::vector<Int>>> Sb(n, std::vector<std::vector<Int>>(p + 1, std::vector<Int>(s + 1, INF)));
    std::vector<std::vector<Int>> Root(p + 1, std::vector<Int>(s + 1, INF));
    K[0][0][0] = 0;
    for(int q = 1; q <= p; ++q)
    {
        // subtrees with q planes: root + children with q-1 planes
        for(int tau = 0; tau <= T; ++tau)
            for(int jk = 0; jk <= s; ++jk)
            {
                const Int kv = K[tau][q - 1][jk];
                if(inf(kv)) continue;
                for(int r = 1; jk + r <= s; r += 2)
                {
                    // tree root without parent
                    if(T - tau >= 0 && !inf(G[r][T - tau]))
                        Root[q][jk + r] = std::min(Root[q][jk + r], kv + G[r][T - tau]);
                    for(int a = 0; a < n; ++a)
                    {
                        const int budget = T - (int)in.d[a] - tau;
                        if(budget < 0 || jk + 1 + r > s || inf(G[r][budget])) continue;
                        Int& cell = Sb[a][q][jk + 1 + r];
                        cell = std::min(cell, in.c[a] + kv + G[r][budget]);
                    }
                }
            }
        if(q > p - 1) break;
        // K with q child planes, from items (b, qc, jc) with qc <= q
        for(int tau = 0; tau <= T; ++tau)
            for(int j = 1; j <= s; ++j)
            {
                Int best = INF;
                for(int b = 0; b < n; ++b)
                {
                    const int prevTau = tau - (int)in.d[b];
                    if(prevTau < 0) continue;
                    for(int qc = 1; qc <= q; ++qc)
                        for(int jc = 1; 1 + jc <= j; ++jc)
                        {
                            const Int sv = Sb[b][qc][jc]; if(inf(sv)) continue;
                            const Int kv = K[prevTau][q - qc][j - 1 - jc]; if(inf(kv)) continue;
                            best = std::min(best, kv + in.c[b] + sv);
                        }
                }
                K[tau][q][j] = std::min(K[tau][q][j], best);
            }
    }
    // forest = multiset of trees covering p planes and s landings
    std::vector<std::vector<Int>> Fo(p + 1, std::vector<Int>(s + 1, INF));
    Fo[0][0] = 0;
    for(int P = 1; P <= p; ++P)
        for(int J = 1; J <= s; ++J)
            for(int q = 1; q <= P; ++q)
                for(int j = 1; j <= J; ++j)
                    if(!inf(Root[q][j]) && !inf(Fo[P - q][J - j]))
                        Fo[P][J] = std::min(Fo[P][J], Fo[P - q][J - j] + Root[q][j]);
    return Fo[p][s];
}

int main(int argc, char** argv)
{
    if(argc < 5) return 2;
    auto parseL = [](const std::string& str) { std::vector<Int> v; std::size_t pos = 0; while(pos < str.size()) { std::size_t q = str.find(',', pos); if(q == std::string::npos) q = str.size(); v.push_back(std::atoll(str.substr(pos, q - pos).c_str())); pos = q + 1; } return v; };
    Inst in; in.d = parseL(argv[1]); in.c = parseL(argv[2]); in.t = std::atoi(argv[3]); in.p = std::atoi(argv[4]);
    const bool verbose = argc > 5 && std::string(argv[5]) == "v";
    const int n = in.n(), s = in.s();
    const Int dmax = *std::max_element(in.d.begin(), in.d.end());
    const int Tmax = (int)(dmax * (s - in.p + 1));
    // enumeration: E_enum[T] = min cost over X with M(X) <= 2T
    std::vector<Int> Eenum(Tmax + 1, INF);
    std::vector<int> x(n, 0);
    std::function<void(int, int)> rec = [&](int i, int left)
    {
        if(i == n - 1)
        {
            x[i] = left; Int cost = 0; for(int k = 0; k < n; ++k) cost += x[k] * in.c[k];
            PartitionSearch ps(in, x, lowerBound(in, x)); const Int m = ps.run();
            if(m < INF) for(int T = (int)((m + 1) / 2); T <= Tmax; ++T) Eenum[T] = std::min(Eenum[T], cost);
            x[i] = 0; return;
        }
        for(int v = left; v >= 0; --v) { x[i] = v; rec(i + 1, left - v); }
        x[i] = 0;
    };
    rec(0, s);
    std::vector<std::vector<Int>> G(s + 1, std::vector<Int>(Tmax + 1, INF));
    for(int T = 0; T <= Tmax; ++T) G[0][T] = 0;
    for(int m = 1; m <= s; ++m) for(int T = 0; T <= Tmax; ++T) for(int i = 0; i < n; ++i)
        if(T >= in.d[i] && G[m - 1][T - in.d[i]] < INF) G[m][T] = std::min(G[m][T], in.c[i] + G[m - 1][T - in.d[i]]);
    int mismatches = 0;
    for(int T = 0; T <= Tmax; ++T)
    {
        const Int et = treeDP(in, G, T);
        if(et != Eenum[T]) { ++mismatches; if(verbose) std::printf("T=%d tree=%lld enum=%lld\n", T, et >= INF ? -1LL : (long long)et, Eenum[T] >= INF ? -1LL : (long long)Eenum[T]); }
    }
    std::printf("%d %d\n", Tmax + 1, mismatches);
    return 0;
}
