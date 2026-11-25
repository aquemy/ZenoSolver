// Front of all simple plans with clean journeys (doc/theory/exact-front.md, revision 2, Lemma 4.3(a)): every flight joins
// a hub and a central city, every journey is C_I -> x on the first flight of an A or B segment followed by
// x -> C_G on the second flight of an A or Bbar segment at the same city. Under (A1-NS) every plan is weakly
// dominated by such a plan (Step 1 of Theorem 5.3, and the cleaning of revision 2's Lemma 3.1), so this front is the front of all plans when
// the plans with at most s + extra landings suffice.
//
// Unlike role configurations, hand-offs may involve A segments (a crossing that drops its passenger and
// picks up another one, or flies one leg empty). Timing is exact: every flight departs as early as its
// plane and its passenger allow (earliest start is optimal for fixed routes and journeys).
//
// Usage: simple_plans <d1,..> <dbar1,..> <c1,..> <t> <p> [extra] [nowait]
// With "nowait", timing is ignored (makespan = largest flight time): the no-waiting front of the same plans.
// Prints "cost makespan" lines of the front over plans with s .. s+extra segments.
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <string>
#include <vector>

using Int = long long;
const Int INF = (Int)4e18;

struct Seg { int type, city; };   // type: 0 = A, 1 = Abar, 2 = B, 3 = Bbar
static int n, t, p, s;
static std::vector<Int> d, db, c;
static bool nowait = false;

static std::vector<Int> parse(const std::string& str)
{
    std::vector<Int> v; std::size_t pos = 0;
    while(pos < str.size()) { std::size_t q = str.find(',', pos); if(q == std::string::npos) q = str.size(); v.push_back(std::atoll(str.substr(pos, q - pos).c_str())); pos = q + 1; }
    return v;
}
// duration of the first and second flight of a segment
static Int dur0(const Seg& g) { return (g.type == 0 || g.type == 2) ? d[g.city] : db[g.city]; }
static Int dur1(const Seg& g) { return (g.type == 0 || g.type == 3) ? db[g.city] : d[g.city]; }
static bool hasOut(const Seg& g) { return g.type == 0 || g.type == 2; }   // first flight from C_I
static bool hasIn(const Seg& g) { return g.type == 0 || g.type == 3; }    // second flight to C_G

// all side-consistent routes of length L from C_I to C_G
static void routes(int L, std::vector<std::vector<Seg>>& out)
{
    std::vector<Seg> cur;
    std::function<void(int, bool)> rec = [&](int left, bool west)
    {
        if(left == 0) { if(!west) out.push_back(cur); return; }
        for(int ty = 0; ty < 4; ++ty)
        {
            bool ok = west ? (ty == 0 || ty == 2) : (ty == 1 || ty == 3);
            if(!ok) continue;
            bool nw = (ty == 0) ? false : (ty == 1) ? true : west;
            for(int x = 0; x < n; ++x) { cur.push_back({ty, x}); rec(left - 1, nw); cur.pop_back(); }
        }
    };
    rec(L, true);
}

struct Slot { int plane, seg; };
static std::map<Int, Int> best;   // cost -> least makespan

// earliest-start simulation; inSrc[plane][seg] = index of the out-slot whose passenger the second flight of
// this segment carries (-1: empty or through); returns makespan or INF on deadlock
static Int simulate(const std::vector<std::vector<Seg>>& R, const std::vector<std::vector<int>>& inSrc,
                    const std::vector<Slot>& outs)
{
    const int P = (int)R.size();
    std::vector<std::vector<Int>> arr0(P);   // arrival time of the first flight of each segment
    for(int k = 0; k < P; ++k) arr0[k].assign(R[k].size(), -1);
    std::vector<std::size_t> next(P, 0); std::vector<Int> time(P, 0);
    bool progress = true;
    while(progress)
    {
        progress = false;
        for(int k = 0; k < P; ++k)
            while(next[k] < R[k].size())
            {
                const Seg& g = R[k][next[k]];
                const Int a0 = time[k] + dur0(g);
                Int dep = a0;
                const int src = inSrc[k][next[k]];
                if(src >= 0)
                {
                    const Slot& o = outs[src];
                    if(o.plane == k && o.seg == (int)next[k]) {}
                    else
                    {
                        const Int a = arr0[o.plane][o.seg];
                        if(a < 0) break;   // passenger not dropped yet
                        dep = std::max(dep, a);
                    }
                }
                arr0[k][next[k]] = a0;
                time[k] = dep + dur1(g);
                ++next[k]; progress = true;
            }
    }
    Int m = 0;
    for(int k = 0; k < P; ++k) { if(next[k] < R[k].size()) return INF; m = std::max(m, time[k]); }
    return m;
}

static void solveRoutes(const std::vector<std::vector<Seg>>& R)
{
    Int cost = 0, lb = 0;
    for(auto& r : R) { Int ft = 0; for(auto& g : r) { cost += c[g.city]; ft += dur0(g) + dur1(g); } lb = std::max(lb, ft); }
    auto it = best.find(cost);
    if(it != best.end() && it->second <= lb) return;
    // also skip if a cheaper-or-equal cost already reaches lb
    for(auto& kv : best) if(kv.first <= cost && kv.second <= lb) return;
    std::vector<Slot> outs, ins;
    for(int k = 0; k < (int)R.size(); ++k)
        for(int j = 0; j < (int)R[k].size(); ++j)
        {
            if(hasOut(R[k][j])) outs.push_back({k, j});
            if(hasIn(R[k][j])) ins.push_back({k, j});
        }
    if((int)outs.size() < t || (int)ins.size() < t) return;
    if(nowait)   // ignore timing: makespan = largest flight time, if t passengers fit city by city
    {
        int fit = 0;
        for(int x = 0; x < n; ++x)
        {
            int o = 0, q = 0;
            for(auto& sl : outs) o += R[sl.plane][sl.seg].city == x;
            for(auto& sl : ins) q += R[sl.plane][sl.seg].city == x;
            fit += std::min(o, q);
        }
        if(fit >= t && (it == best.end() || lb < it->second)) best[cost] = lb;
        return;
    }
    std::vector<std::vector<int>> inSrc(R.size());
    for(int k = 0; k < (int)R.size(); ++k) inSrc[k].assign(R[k].size(), -1);
    std::vector<char> usedIn(ins.size(), 0);
    Int bestHere = (it == best.end()) ? INF : it->second;
    // assign passengers: each out-slot is either unused or matched to an unused in-slot at the same city
    // (same segment = through; same plane = later segment), exactly t matched
    std::function<void(std::size_t, int)> rec = [&](std::size_t oi, int matched)
    {
        if(bestHere <= lb) return;
        if(matched == t)
        {
            const Int m = simulate(R, inSrc, outs);
            if(m < bestHere) bestHere = m;
            return;
        }
        if(oi == outs.size() || matched + (int)(outs.size() - oi) < t) return;
        const Slot& o = outs[oi];
        for(std::size_t ii = 0; ii < ins.size(); ++ii)
        {
            if(usedIn[ii]) continue;
            const Slot& q = ins[ii];
            if(R[q.plane][q.seg].city != R[o.plane][o.seg].city) continue;
            if(q.plane == o.plane && q.seg < o.seg) continue;
            usedIn[ii] = 1; inSrc[q.plane][q.seg] = (int)oi;
            rec(oi + 1, matched + 1);
            usedIn[ii] = 0; inSrc[q.plane][q.seg] = -1;
        }
        rec(oi + 1, matched);   // out-slot flies empty
    };
    rec(0, 0);
    if(bestHere < INF && (it == best.end() || bestHere < it->second)) best[cost] = bestHere;
}

int main(int argc, char** argv)
{
    if(argc < 6) { std::fprintf(stderr, "usage: simple_plans d dbar c t p [extra]\n"); return 2; }
    d = parse(argv[1]); db = parse(argv[2]); c = parse(argv[3]); t = std::atoi(argv[4]); p = std::atoi(argv[5]);
    const int extra = argc > 6 ? std::atoi(argv[6]) : 0;
    nowait = argc > 7 && std::string(argv[7]) == "nowait";
    n = (int)d.size(); s = 2 * t - p;
    for(int S = s; S <= s + extra; ++S)
    {
        // route length per plane: 1 .. S - (p-1); planes interchangeable: non-decreasing route index
        std::vector<std::vector<std::vector<Seg>>> byLen(S + 1);
        for(int L = 1; L <= S - (p - 1); ++L) routes(L, byLen[L]);
        std::vector<std::pair<int, int>> all;   // (length, index)
        for(int L = 1; L <= S - (p - 1); ++L) for(int i = 0; i < (int)byLen[L].size(); ++i) all.push_back({L, i});
        std::vector<std::vector<Seg>> R;
        std::function<void(int, std::size_t, int)> rec = [&](int k, std::size_t from, int left)
        {
            if(k == p) { if(left == 0) solveRoutes(R); return; }
            for(std::size_t a = from; a < all.size(); ++a)
            {
                const int L = all[a].first;
                if(L > left - (p - 1 - k)) continue;
                R.push_back(byLen[L][all[a].second]);
                rec(k + 1, a, left - L);
                R.pop_back();
            }
        };
        rec(0, 0, S);
    }
    Int bestM = INF;
    for(auto& kv : best) if(kv.second < bestM) { std::printf("%lld %lld\n", kv.first, kv.second); bestM = kv.second; }
    return 0;
}
