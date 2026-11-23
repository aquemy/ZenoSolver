// Numerical checks for the statements of doc/theory/exact-front.md (symmetric case).
// Ground truth: E_enum(T) = min c(X) over |X| = s with an admissible partition (component
// form, checked by union-find) and every group duration <= T, by full enumeration.
// Checked against it, at every level T in [0, Tmax]:
//   tree   : link-forest tree DP (prototype recurrence), all tree sizes
//   treeq  : same, trees restricted to q <= q_max = min(p, t-p+1)
//   sigma  : sigma-DP with |sigma| <= w = min(p-1, t-p) and |H| <= min(m-1, w)
//   sigmaU : sigma-DP without the w restriction
//   L<=E, U3<=U, E<=U3, U==E if q_max<=2, U3==E if q_max<=3
//   ends   : E finite iff T >= dmin*ceil(s/p); E(Thi)=s*cmin, E(Thi-1)>s*cmin, Thi=dcheap*ceil(s/p)
//   dom    : E unchanged after removing dominated cities
//   pareto : Pareto sigma-DP over (cost, max delta) equals the breakpoints of E_enum
//   hB     : for random partitions, brute force over all h: h exists <=> component form;
//            every minimal-support valid h is a forest touching <= min(p-1, t-p) cities;
//            every valid h touches <= t-p cities.
// Usage: theorychecks <d1,..> <c1,..> <t> <p> <seed>
// Output: one line "levels key=mismatches ..."
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <numeric>
#include <random>
#include <string>
#include <vector>

using Int = long long;
const Int INF = (Int)4e18;
struct Inst { std::vector<Int> d, c; int t = 0, p = 0; int n() const { return (int)d.size(); } int s() const { return 2 * t - p; } };

static std::vector<std::vector<Int>> buildG(const Inst& in, int mmax, int Tmax)
{
    std::vector<std::vector<Int>> G(mmax + 1, std::vector<Int>(Tmax + 1, INF));
    for(int T = 0; T <= Tmax; ++T) G[0][T] = 0;
    for(int m = 1; m <= mmax; ++m) for(int T = 0; T <= Tmax; ++T) for(int i = 0; i < in.n(); ++i)
        if(T >= in.d[i] && G[m - 1][T - in.d[i]] < INF) G[m][T] = std::min(G[m][T], in.c[i] + G[m - 1][T - in.d[i]]);
    return G;
}
static Int g(const std::vector<std::vector<Int>>& G, int m, Int T) { if(T < 0 || m < 0 || m >= (int)G.size()) return INF; if(T >= (Int)G[0].size()) T = (Int)G[0].size() - 1; return G[m][T]; }

// ---------------------------------------------------------------- enumeration
struct PartitionSearch
{
    const Inst& in; std::vector<int> jobs, assigned; std::vector<std::vector<int>> count; std::vector<Int> load; std::vector<int> size;
    Int best = INF;
    PartitionSearch(const Inst& i, const std::vector<int>& x) : in(i), count(i.p, std::vector<int>(i.n(), 0)), load(i.p, 0), size(i.p, 0)
    {
        for(int c = 0; c < in.n(); ++c) for(int k = 0; k < x[c]; ++k) jobs.push_back(c);
        std::sort(jobs.begin(), jobs.end(), [&](int a, int b) { return in.d[a] != in.d[b] ? in.d[a] > in.d[b] : a < b; });
        assigned.assign(jobs.size(), 0);
    }
    bool admissible() const
    {
        const int p = in.p, n = in.n(); std::vector<int> par(p + n); std::iota(par.begin(), par.end(), 0);
        std::function<int(int)> f = [&](int v) { return par[v] == v ? v : par[v] = f(par[v]); };
        for(int k = 0; k < p; ++k) for(int c = 0; c < n; ++c) if(count[k][c] > 0) par[f(k)] = f(p + c);
        std::vector<int> ev(p + n, 0); for(int k = 0; k < p; ++k) if(size[k] % 2 == 0) ++ev[f(k)];
        for(int v : ev) if(v % 2) return false; return true;
    }
    void rec(std::size_t j, int used)
    {
        if(j == jobs.size()) { if(used == in.p && admissible()) best = std::min(best, *std::max_element(load.begin(), load.end())); return; }
        if((int)(jobs.size() - j) < in.p - used) return;
        const int from = (j > 0 && jobs[j] == jobs[j - 1]) ? assigned[j - 1] : 0;
        for(int k = from; k < std::min(used + 1, in.p); ++k)
        {
            const Int w = in.d[jobs[j]];
            if(load[k] + w >= best) continue;
            load[k] += w; ++size[k]; ++count[k][jobs[j]]; assigned[j] = k;
            rec(j + 1, std::max(used, k + 1));
            load[k] -= w; --size[k]; --count[k][jobs[j]];
        }
    }
};
// E_enum[T] (durations, not loads)
static std::vector<Int> enumerate(const Inst& in, int Tmax)
{
    const int n = in.n(), s = in.s(); std::vector<Int> E(Tmax + 1, INF); std::vector<int> x(n, 0);
    std::function<void(int, int)> rec = [&](int i, int left)
    {
        if(i == n - 1)
        {
            x[i] = left; Int cost = 0; for(int k = 0; k < n; ++k) cost += x[k] * in.c[k];
            PartitionSearch ps(in, x); ps.rec(0, 0);
            if(ps.best < INF) for(Int T = ps.best; T <= Tmax; ++T) E[T] = std::min(E[T], cost);
            x[i] = 0; return;
        }
        for(int v = left; v >= 0; --v) { x[i] = v; rec(i + 1, left - v); }
        x[i] = 0;
    };
    rec(0, s); return E;
}

// ---------------------------------------------------------------- tree DP (prototype recurrence)
static Int treeDP(const Inst& in, const std::vector<std::vector<Int>>& G, int T, int qcap)
{
    const int p = in.p, s = in.s(), n = in.n(); auto inf = [](Int v) { return v >= INF; };
    std::vector<std::vector<std::vector<Int>>> K(T + 1, std::vector<std::vector<Int>>(p, std::vector<Int>(s + 1, INF)));
    std::vector<std::vector<std::vector<Int>>> Sb(n, std::vector<std::vector<Int>>(p + 1, std::vector<Int>(s + 1, INF)));
    std::vector<std::vector<Int>> Root(p + 1, std::vector<Int>(s + 1, INF));
    K[0][0][0] = 0;
    for(int q = 1; q <= std::min(p, qcap); ++q)
    {
        for(int tau = 0; tau <= T; ++tau) for(int jk = 0; jk <= s; ++jk)
        {
            const Int kv = K[tau][q - 1][jk]; if(inf(kv)) continue;
            for(int r = 1; jk + r <= s; r += 2)
            {
                if(!inf(g(G, r, T - tau))) Root[q][jk + r] = std::min(Root[q][jk + r], kv + g(G, r, T - tau));
                for(int a = 0; a < n; ++a)
                {
                    const Int budget = T - in.d[a] - tau;
                    if(budget < 0 || jk + 1 + r > s || inf(g(G, r, budget))) continue;
                    Int& cell = Sb[a][q][jk + 1 + r]; cell = std::min(cell, in.c[a] + kv + g(G, r, budget));
                }
            }
        }
        if(q > p - 1) break;
        for(int tau = 0; tau <= T; ++tau) for(int j = 1; j <= s; ++j)
        {
            Int best = INF;
            for(int b = 0; b < n; ++b)
            {
                const Int pt = tau - in.d[b]; if(pt < 0) continue;
                for(int qc = 1; qc <= q; ++qc) for(int jc = 1; 1 + jc <= j; ++jc)
                {
                    const Int sv = Sb[b][qc][jc]; if(inf(sv)) continue;
                    const Int kv = K[pt][q - qc][j - 1 - jc]; if(inf(kv)) continue;
                    best = std::min(best, kv + in.c[b] + sv);
                }
            }
            K[tau][q][j] = std::min(K[tau][q][j], best);
        }
    }
    std::vector<std::vector<Int>> Fo(p + 1, std::vector<Int>(s + 1, INF)); Fo[0][0] = 0;
    for(int P = 1; P <= p; ++P) for(int J = 1; J <= s; ++J) for(int q = 1; q <= P; ++q) for(int j = 1; j <= J; ++j)
        if(!inf(Root[q][j]) && !inf(Fo[P - q][J - j])) Fo[P][J] = std::min(Fo[P][J], Fo[P - q][J - j] + Root[q][j]);
    return Fo[p][s];
}

// ---------------------------------------------------------------- sigma DP
static Int sigmaDP(const Inst& in, const std::vector<std::vector<Int>>& G, int T, int w)
{
    const int n = in.n(), p = in.p, s = in.s(), M = 1 << n, mhat = s - p + 1;
    std::vector<Int> cur((s + 1) * M, INF), nxt; cur[0] = 0;
    std::vector<Int> dH(M, 0), cH(M, 0); std::vector<int> pc(M, 0);
    for(int H = 1; H < M; ++H) { int i = __builtin_ctz(H); dH[H] = dH[H & (H - 1)] + in.d[i]; cH[H] = cH[H & (H - 1)] + in.c[i]; pc[H] = pc[H & (H - 1)] + 1; }
    for(int k = 0; k < p; ++k)
    {
        nxt.assign((s + 1) * M, INF);
        for(int j = 0; j <= s; ++j) for(int sg = 0; sg < M; ++sg)
        {
            const Int v = cur[j * M + sg]; if(v >= INF) continue;
            for(int m = 1; m <= mhat && j + m <= s; ++m)
                for(int H = 0; H < M; ++H)
                {
                    if(pc[H] > std::min(m - 1, w) || (pc[H] % 2) != ((m + 1) % 2)) continue;
                    const int ns = sg ^ H; if(pc[ns] > w) continue;
                    const Int gv = g(G, m - pc[H], T - dH[H]); if(gv >= INF) continue;
                    Int& cell = nxt[(j + m) * M + ns]; cell = std::min(cell, v + cH[H] + gv);
                }
        }
        cur.swap(nxt);
    }
    return cur[s * M + 0];
}

// Pareto sigma-DP over (cost, max delta), all levels at once; delta capped at Tmax.
using PS = std::vector<std::pair<Int, Int>>;
static PS paretoMin(PS v)
{
    std::sort(v.begin(), v.end()); PS r; Int bestT = INF;
    for(auto& e : v) if(e.second < bestT) { r.push_back(e); bestT = e.second; }
    return r;
}
static PS paretoSigma(const Inst& in, const std::vector<std::vector<Int>>& G, int Tmax, int w)
{
    const int n = in.n(), p = in.p, s = in.s(), M = 1 << n, mhat = s - p + 1;
    std::vector<Int> dH(M, 0), cH(M, 0); std::vector<int> pc(M, 0);
    for(int H = 1; H < M; ++H) { int i = __builtin_ctz(H); dH[H] = dH[H & (H - 1)] + in.d[i]; cH[H] = cH[H & (H - 1)] + in.c[i]; pc[H] = pc[H & (H - 1)] + 1; }
    // option staircases: opt[m][H] = Min{(cH + G[r][tau], dH + tau)}
    std::vector<std::vector<PS>> opt(mhat + 1, std::vector<PS>(M));
    for(int m = 1; m <= mhat; ++m) for(int H = 0; H < M; ++H)
    {
        if(pc[H] > std::min(m - 1, w) || (pc[H] % 2) != ((m + 1) % 2)) continue;
        PS v; for(Int tau = 0; dH[H] + tau <= Tmax; ++tau) { Int gv = g(G, m - pc[H], tau); if(gv < INF) v.push_back({cH[H] + gv, dH[H] + tau}); }
        opt[m][H] = paretoMin(v);
    }
    std::vector<PS> cur((s + 1) * M), nxt; cur[0] = {{0, 0}};
    for(int k = 0; k < p; ++k)
    {
        nxt.assign((s + 1) * M, PS{});
        for(int j = 0; j <= s; ++j) for(int sg = 0; sg < M; ++sg)
        {
            const PS& A = cur[j * M + sg]; if(A.empty()) continue;
            for(int m = 1; m <= mhat && j + m <= s; ++m) for(int H = 0; H < M; ++H)
            {
                const PS& B = opt[m][H]; if(B.empty()) continue;
                const int ns = sg ^ H; if(pc[ns] > w) continue;
                PS& cell = nxt[(j + m) * M + ns];
                for(auto& a : A) for(auto& b : B) cell.push_back({a.first + b.first, std::max(a.second, b.second)});
            }
        }
        for(auto& cell : nxt) if(!cell.empty()) cell = paretoMin(cell);
        cur.swap(nxt);
    }
    return cur[s * M + 0];
}

// ---------------------------------------------------------------- gadget bounds
// kind 0: L (any single plane), 1: U (odd singles + pairs), 2: U3 (+ 3-chains)
static Int gadgetBound(const Inst& in, const std::vector<std::vector<Int>>& G, int T, int kind)
{
    const int n = in.n(), p = in.p, s = in.s(), mhat = s - p + 1;
    struct Gd { int q, j; Int c; }; std::vector<Gd> gs;
    for(int m = 1; m <= mhat; ++m) if((kind == 0 || (m & 1)) && g(G, m, T) < INF) gs.push_back({1, m, g(G, m, T)});
    if(kind >= 1 && kind <= 2)
    {
        std::vector<Int> pairJ(s + 1, INF);
        for(int i = 0; i < n; ++i) for(int a = 2; a <= mhat; a += 2) for(int b = 2; a + b <= s && b <= mhat; b += 2)
        {
            Int x = g(G, a - 1, T - in.d[i]), y = g(G, b - 1, T - in.d[i]); if(x >= INF || y >= INF) continue;
            pairJ[a + b] = std::min(pairJ[a + b], 2 * in.c[i] + x + y);
        }
        for(int j = 0; j <= s; ++j) if(pairJ[j] < INF) gs.push_back({2, j, pairJ[j]});
    }
    if(kind >= 2)
    {
        std::vector<Int> ch(s + 1, INF);
        for(int i = 0; i < n; ++i) for(int k = 0; k < n; ++k)
            for(int a = 2; a <= mhat; a += 2) for(int b = 3; b <= mhat; b += 2) for(int c = 2; c <= mhat && a + b + c <= s; c += 2)
            {
                Int x = g(G, a - 1, T - in.d[i]), y = g(G, b - 2, T - in.d[i] - in.d[k]), z = g(G, c - 1, T - in.d[k]);
                if(x >= INF || y >= INF || z >= INF) continue;
                ch[a + b + c] = std::min(ch[a + b + c], 2 * in.c[i] + 2 * in.c[k] + x + y + z);
            }
        for(int j = 0; j <= s; ++j) if(ch[j] < INF) gs.push_back({3, j, ch[j]});
    }
    std::vector<std::vector<Int>> F(p + 1, std::vector<Int>(s + 1, INF)); F[0][0] = 0;
    for(int P = 1; P <= p; ++P) for(int J = 1; J <= s; ++J) for(auto& gd : gs)
        if(gd.q <= P && gd.j <= J && F[P - gd.q][J - gd.j] < INF) F[P][J] = std::min(F[P][J], F[P - gd.q][J - gd.j] + gd.c);
    return F[p][s];
}

// ---------------------------------------------------------------- brute force over h
struct HStats { long cases = 0, existMismatch = 0, minSupportNotForest = 0, minSupportTooMany = 0, anyTooManyTp = 0; };
static bool componentAdmissible(const std::vector<std::vector<int>>& cnt, int n)
{
    const int p = (int)cnt.size(); std::vector<int> par(p + n); std::iota(par.begin(), par.end(), 0);
    std::function<int(int)> f = [&](int v) { return par[v] == v ? v : par[v] = f(par[v]); };
    for(int k = 0; k < p; ++k) for(int c = 0; c < n; ++c) if(cnt[k][c] > 0) par[f(k)] = f(p + c);
    std::vector<int> ev(p + n, 0);
    for(int k = 0; k < p; ++k) { int sz = 0; for(int c = 0; c < n; ++c) sz += cnt[k][c]; if(sz % 2 == 0) ++ev[f(k)]; }
    for(int v : ev) if(v % 2) return false; return true;
}
static void hCheck(const std::vector<std::vector<int>>& cnt, int n, int t, HStats& st)
{
    const int p = (int)cnt.size();
    std::vector<std::pair<int, int>> cells; for(int k = 0; k < p; ++k) for(int c = 0; c < n; ++c) if(cnt[k][c] > 0) cells.push_back({k, c});
    const int E = (int)cells.size(); if(E > 18) return;
    std::vector<int> sz(p, 0); for(int k = 0; k < p; ++k) for(int c = 0; c < n; ++c) sz[k] += cnt[k][c];
    int bestSupp = 1 << 30; std::vector<int> minMasks; bool any = false;
    for(int mask = 0; mask < (1 << E); ++mask)
    {
        std::vector<int> row(p, 0), col(n, 0);
        for(int e = 0; e < E; ++e) if(mask >> e & 1) { ++row[cells[e].first]; ++col[cells[e].second]; }
        bool ok = true;
        for(int k = 0; k < p && ok; ++k) if(row[k] % 2 != (sz[k] + 1) % 2) ok = false;
        for(int c = 0; c < n && ok; ++c) if(col[c] % 2) ok = false;
        if(!ok) continue;
        any = true;
        int touched = 0; for(int c = 0; c < n; ++c) if(col[c]) ++touched;
        if(touched > t - p) ++st.anyTooManyTp;
        int supp = __builtin_popcount(mask);
        if(supp < bestSupp) { bestSupp = supp; minMasks.clear(); }
        if(supp == bestSupp) minMasks.push_back(mask);
    }
    ++st.cases;
    if(any != componentAdmissible(cnt, n)) ++st.existMismatch;
    for(int mask : minMasks)
    {
        std::vector<int> par(p + n); std::iota(par.begin(), par.end(), 0);
        std::function<int(int)> f = [&](int v) { return par[v] == v ? v : par[v] = f(par[v]); };
        bool forest = true; std::vector<int> col(n, 0);
        for(int e = 0; e < E; ++e) if(mask >> e & 1)
        {
            int a = f(cells[e].first), b = f(p + cells[e].second); if(a == b) forest = false; else par[a] = b; ++col[cells[e].second];
        }
        int touched = 0; for(int c = 0; c < n; ++c) if(col[c]) ++touched;
        if(!forest) ++st.minSupportNotForest;
        if(touched > std::min(p - 1, t - p)) ++st.minSupportTooMany;
    }
}

int main(int argc, char** argv)
{
    if(argc < 6) return 2;
    auto parseL = [](const std::string& str) { std::vector<Int> v; std::size_t pos = 0; while(pos < str.size()) { std::size_t q = str.find(',', pos); if(q == std::string::npos) q = str.size(); v.push_back(std::atoll(str.substr(pos, q - pos).c_str())); pos = q + 1; } return v; };
    Inst in; in.d = parseL(argv[1]); in.c = parseL(argv[2]); in.t = std::atoi(argv[3]); in.p = std::atoi(argv[4]);
    const unsigned seed = (unsigned)std::atoi(argv[5]);
    const int n = in.n(), s = in.s(), p = in.p, t = in.t, mhat = s - p + 1;
    const Int dmax = *std::max_element(in.d.begin(), in.d.end());
    const int Tmax = (int)(dmax * mhat);
    const auto G = buildG(in, s, Tmax);
    const int qmax = std::min(p, t - p + 1), w = std::min(p - 1, t - p);
    if(std::string(argv[5]) == "Eonly")     // print "T L(T) E(T)" with E from the tree DP, T <= dmax*ceil(s/p)
    {
        const Int cs = (s + p - 1) / p;
        for(Int T = 0; T <= std::min<Int>(Tmax, dmax * cs); ++T)
        {
            const Int e = treeDP(in, G, (int)T, qmax), L = gadgetBound(in, G, (int)T, 0);
            std::printf("%lld %lld %lld\n", (long long)T, L >= INF ? -1LL : (long long)L, e >= INF ? -1LL : (long long)e);
        }
        return 0;
    }
    if(std::string(argv[5]) == "nogap")     // larger instances: E from the tree DP; gaps of U, U3, odd-only, L
    {
        const Int dmin = *std::min_element(in.d.begin(), in.d.end());
        const Int cmin = *std::min_element(in.c.begin(), in.c.end());
        Int dcheap = INF; for(int i = 0; i < n; ++i) if(in.c[i] == cmin) dcheap = std::min(dcheap, in.d[i]);
        const Int cs = (s + p - 1) / p;
        long lv = 0, gU = 0, gU3 = 0, gO = 0, gL = 0;
        for(Int T = dmin * cs; T <= dcheap * cs; ++T)
        {
            ++lv; const Int e = treeDP(in, G, (int)T, qmax);
            if(gadgetBound(in, G, (int)T, 1) != e) ++gU;
            if(gadgetBound(in, G, (int)T, 2) != e) ++gU3;
            if(gadgetBound(in, G, (int)T, 3) != e) ++gO;
            if(gadgetBound(in, G, (int)T, 0) != e) ++gL;
        }
        std::printf("%ld gapU=%ld gapU3=%ld gapOdd=%ld gapL=%ld\n", lv, gU, gU3, gO, gL);
        return 0;
    }
    const auto E = enumerate(in, Tmax);
    if(std::string(argv[5]) == "bracket")   // print "T L(T) E(T)" (-1 = infinite)
    {
        for(int T = 0; T <= Tmax; ++T)
        {
            const Int L = gadgetBound(in, G, T, 0);
            std::printf("%d %lld %lld\n", T, L >= INF ? -1LL : (long long)L, E[T] >= INF ? -1LL : (long long)E[T]);
        }
        return 0;
    }
    std::map<std::string, long> bad; long levels = 0;
    for(const char* k : {"tree","treeq","sigma","sigmaU","L<=E","E<=U3","U3<=U","U=E","U3=E","endsLo","endsHi","endsMin","dom","pareto"}) bad[k] = 0;
    for(int T = 0; T <= Tmax; ++T)
    {
        ++levels;
        const Int e = E[T];
        if(treeDP(in, G, T, p) != e) ++bad["tree"];
        if(treeDP(in, G, T, qmax) != e) ++bad["treeq"];
        if(sigmaDP(in, G, T, w) != e) ++bad["sigma"];
        if(sigmaDP(in, G, T, n) != e) ++bad["sigmaU"];
        const Int L = gadgetBound(in, G, T, 0), U = gadgetBound(in, G, T, 1), U3 = gadgetBound(in, G, T, 2);
        if(L > e) ++bad["L<=E"];
        if(e > U3) ++bad["E<=U3"];
        if(U3 > U) ++bad["U3<=U"];
        if(qmax <= 2 && U != e) ++bad["U=E"];
        if(L < e) ++bad["info_gapL_q" + std::to_string(qmax)];
        if(U > e) ++bad["info_gapU_q" + std::to_string(qmax)];
        if(U3 > e) ++bad["info_gapU3_q" + std::to_string(qmax)];
        if(qmax <= 3 && U3 != e) ++bad["U3=E"];
    }
    // closed-form ends
    {
        const Int dmin = *std::min_element(in.d.begin(), in.d.end());
        const Int cmin = *std::min_element(in.c.begin(), in.c.end());
        Int dcheap = INF; for(int i = 0; i < n; ++i) if(in.c[i] == cmin) dcheap = std::min(dcheap, in.d[i]);
        const Int cs = (s + p - 1) / p;
        const Int Tlo = dmin * cs, Thi = dcheap * cs;
        for(int T = 0; T <= Tmax; ++T) if((E[T] < INF) != (T >= Tlo)) { ++bad["endsLo"]; break; }
        if(Thi > Tmax || E[Thi] != s * cmin || (Thi > 0 && E[Thi - 1] <= s * cmin)) ++bad["endsHi"];
        for(int T = 0; T <= Tmax; ++T) if(E[T] < s * cmin) { ++bad["endsMin"]; break; }
    }
    // dominance
    {
        Inst r; r.t = t; r.p = p;
        for(int i = 0; i < n; ++i)
        {
            bool dom = false;
            for(int j = 0; j < n && !dom; ++j) if(j != i && in.d[j] <= in.d[i] && in.c[j] <= in.c[i] && (in.d[j] < in.d[i] || in.c[j] < in.c[i] || j < i)) dom = true;
            if(!dom) { r.d.push_back(in.d[i]); r.c.push_back(in.c[i]); }
        }
        const auto Er = enumerate(r, Tmax);
        if(Er != E) ++bad["dom"];
    }
    // Pareto variant
    {
        PS front; Int prev = INF;
        for(int T = 0; T <= Tmax; ++T) if(E[T] < prev) { front.push_back({E[T], T}); prev = E[T]; }
        PS ps = paretoSigma(in, G, Tmax, w);
        std::sort(front.begin(), front.end());
        if(ps != front) ++bad["pareto"];
    }
    // brute force over h on random partitions of random multisets of size s
    HStats hs; std::mt19937 rng(seed);
    for(int trial = 0; trial < 40; ++trial)
    {
        std::vector<std::vector<int>> cnt(p, std::vector<int>(n, 0));
        // each plane gets >= 1 landing
        for(int k = 0; k < p; ++k) ++cnt[k][rng() % n];
        for(int l = p; l < s; ++l) ++cnt[rng() % p][rng() % n];
        hCheck(cnt, n, t, hs);
    }
    bad["hExist"] += hs.existMismatch; bad["hForest"] += hs.minSupportNotForest; bad["hMinTouched"] += hs.minSupportTooMany; bad["hAnyTp"] += hs.anyTooManyTp;
    std::printf("%ld hcases=%ld", levels, hs.cases);
    for(auto& kv : bad) std::printf(" %s=%ld", kv.first.c_str(), kv.second);
    std::printf("\n");
    return 0;
}
