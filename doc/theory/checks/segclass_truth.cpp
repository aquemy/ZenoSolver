// Exhaustive search over plans of tiny MultiZenoTravel instances, as in truth.cpp, with a central table
// given explicitly and the plans restricted to a class of segments (doc/theory/exact-front.md, §6.4).
//
// A segment runs from a hub to a hub through central cities (§2). The class says which segments may
// land in two or more central cities, by their start hub, end hub and largest number of central
// landings; segments with one central landing are always allowed. Tokens, joined by '+':
//   none          no segment with two or more central landings (simple plans: role configurations)
//   all           every segment
//   <s><e><m>     segments from hub s to hub e (I or G) with at most m central landings, e.g.
//                 GI2 = shuttles C_G -> i -> j -> C_I, IG2 = crossings C_I -> i -> j -> C_G,
//                 II2, GG2 = drop-off and pick-up segments with one central flight;
//                 m is 1 to 6, or a for no bound
//   <s><e><m>e    the same, and the central flights of segments starting at s carry no passenger,
//                 e.g. IG2e = split crossings C_I -> x -> y -> C_G with an empty middle leg
// With "all" the search is the one of truth.cpp (same model, same caps).
//
// Model: cities I (0), central 1..n, G (n+1). Planes start in I and must end in G; passengers start
// in I and must reach G; capacity one; waiting allowed; integer durations of at least 1. Breadth-first
// over time, one tick per layer; a state reached again with a cost that is not lower is dropped.
//
// usage: segclass_truth <west> <east> <cost> <t> <p> <table> <class> [extraLandings [maxMakespan]]
//   table: none | tight | d12,d13,...,d1n,d23,... (upper triangle, row by row; 0 = no flight)
// prints "cost makespan" lines of the front (makespan decreasing as cost increases)
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

typedef unsigned __int128 Key;
struct KeyHash
{
    std::size_t operator()(const Key& k) const
    {
        const uint64_t a = (uint64_t)k, b = (uint64_t)(k >> 64);
        return (std::size_t)(a * 0x9E3779B97F4A7C15ULL ^ (b + 0x632BE59BD9B4E019ULL + (a << 6) + (a >> 2)));
    }
};

struct Inst
{
    int n = 0, t = 0, p = 0;
    std::vector<int> west, east, cost;
    std::vector<std::vector<int>> D;
    int dur(int a, int b) const   // 0 = no flight
    {
        if(a == b) return 0;
        if(a > b) std::swap(a, b);
        if(a == 0 && b == n + 1) return 0;
        if(a == 0) return west[b - 1];
        if(b == n + 1) return east[a - 1];
        return D[a - 1][b - 1];
    }
};

// Plane code (16 bits): loc 0..2 (location, or destination when flying), flying 3, carry 4,
// start hub 5 (0 = I, 1 = G), central landings in the current segment 6..8 (capped at UNB), rem-1 9..15.
static inline int LOC(int c) { return c & 7; }
static inline int FLY(int c) { return (c >> 3) & 1; }
static inline int CAR(int c) { return (c >> 4) & 1; }
static inline int STA(int c) { return (c >> 5) & 1; }
static const int UNB = 7;   // landing count standing for "no bound"
static inline int SEGM(int c) { return (c >> 6) & 7; }
static inline int REM(int c) { return ((c >> 9) & 127) + 1; }
static inline int mk(int loc, int fly, int carry, int start, int m, int rem)
{
    return loc | (fly << 3) | (carry << 4) | (start << 5) | (m << 6) | ((fly ? rem - 1 : 0) << 9);
}

static int allowM[2][2];   // [start][end] -> largest number of central landings allowed (>= 1)
static bool emptyCentral[2];   // [start]: central flights of such segments carry no passenger

int main(int argc, char** argv)
{
    if(argc < 8) { std::fprintf(stderr, "usage: segclass_truth west east cost t p table class [extra [maxMakespan]]\n"); return 2; }
    auto parse = [](const char* s) { std::vector<int> v; const char* q = s; while(*q) { v.push_back(std::atoi(q)); while(*q && *q != ',') ++q; if(*q) ++q; } return v; };
    Inst in; in.west = parse(argv[1]); in.east = parse(argv[2]); in.cost = parse(argv[3]);
    in.t = std::atoi(argv[4]); in.p = std::atoi(argv[5]); in.n = (int)in.west.size();
    const std::string table = argv[6], cls = argv[7];
    const int extra = argc > 8 ? std::atoi(argv[8]) : 2;
    const int timeCapArg = argc > 9 ? std::atoi(argv[9]) : 0;   // optional: search makespans up to this only
    in.D.assign(in.n, std::vector<int>(in.n, 0));
    if(table == "tight")
    {
        for(int i = 0; i < in.n; ++i) for(int j = 0; j < in.n; ++j) if(i != j)
            in.D[i][j] = std::max({std::abs(in.west[i] - in.west[j]), std::abs(in.east[i] - in.east[j]), 1});
    }
    else if(table != "none")
    {
        std::vector<int> v = parse(table.c_str());
        std::size_t k = 0;
        for(int i = 0; i < in.n; ++i) for(int j = i + 1; j < in.n; ++j)
        {
            if(k >= v.size()) { std::fprintf(stderr, "table too short\n"); return 2; }
            in.D[i][j] = in.D[j][i] = v[k++];
        }
    }
    for(int a = 0; a < 2; ++a) for(int b = 0; b < 2; ++b) allowM[a][b] = 1;
    {
        std::size_t pos = 0;
        while(pos <= cls.size())
        {
            std::size_t q = cls.find('+', pos); if(q == std::string::npos) q = cls.size();
            const std::string tok = cls.substr(pos, q - pos);
            if(tok == "all") { for(auto& r : allowM) for(int& x : r) x = UNB; }
            else if(tok == "none") {}
            else if((tok.size() == 3 || (tok.size() == 4 && tok[3] == 'e')) && (tok[0] == 'I' || tok[0] == 'G') && (tok[1] == 'I' || tok[1] == 'G') && ((tok[2] >= '1' && tok[2] <= '6') || tok[2] == 'a'))
            {
                int& x = allowM[tok[0] == 'G'][tok[1] == 'G']; x = std::max(x, tok[2] == 'a' ? UNB : tok[2] - '0');
                if(tok.size() == 4) emptyCentral[tok[0] == 'G'] = true;   // e.g. IG2e: split crossings, empty middle leg
            }
            else { std::fprintf(stderr, "bad class token %s\n", tok.c_str()); return 2; }
            pos = q + 1;
        }
    }
    const int maxStart[2] = { std::max(allowM[0][0], allowM[0][1]), std::max(allowM[1][0], allowM[1][1]) };
    bool unrestricted = true;
    for(auto& r : allowM) for(int x : r) if(x < UNB) unrestricted = false;
    // The start hub only matters if the class treats the two start hubs differently.
    const bool startMatters = allowM[0][0] != allowM[1][0] || allowM[0][1] != allowM[1][1] || emptyCentral[0] != emptyCentral[1];
    const int dropMask = unrestricted ? ((1 << 5) | (7 << 6)) : (startMatters ? 0 : (1 << 5));
    int RMAX = 1;
    for(int a = 0; a <= in.n + 1; ++a) for(int b = 0; b <= in.n + 1; ++b) RMAX = std::max(RMAX, in.dur(a, b));
    if(in.n > 5 || in.t > 7 || in.p > 4 || RMAX > 128) { std::fprintf(stderr, "instance too large for the state encoding\n"); return 2; }

    const int s = 2 * in.t - in.p;
    const int cmax = std::max(1, *std::max_element(in.cost.begin(), in.cost.end()));
    const int costCap = (s + extra) * cmax;
    int slowest = 0; for(int i = 0; i < in.n; ++i) slowest = std::max(slowest, in.west[i] + in.east[i]);
    const int timeCap = timeCapArg > 0 ? std::min(timeCapArg, s * slowest) : s * slowest;
    const int G = in.n + 1;

    struct St { std::vector<int> plane; std::vector<int> pax; int delivered; };
    auto encode = [&](const St& st) {
        Key k = 0;
        for(int c : st.plane) k = (k << 16) | (Key)c;
        for(int c : st.pax) k = (k << 3) | (Key)c;
        return (k << 3) | (Key)st.delivered;
    };
    auto decode = [&](Key k) {
        St st; st.delivered = (int)(k & 7); k >>= 3;
        st.pax.assign(in.n + 1, 0);
        for(int i = in.n; i >= 0; --i) { st.pax[i] = (int)(k & 7); k >>= 3; }
        st.plane.assign(in.p, 0);
        for(int i = in.p - 1; i >= 0; --i) { st.plane[i] = (int)(k & 0xFFFF); k >>= 16; }
        return st;
    };
    St start; start.plane.assign(in.p, mk(0, 0, 0, 0, 0, 0)); start.pax.assign(in.n + 1, 0); start.pax[0] = in.t; start.delivered = 0;
    std::unordered_map<Key, int, KeyHash> seen, layer, next;
    layer[encode(start)] = 0; seen[encode(start)] = 0;
    std::map<int, int> bestTime;
    long expanded = 0;

    for(int tau = 0; tau <= timeCap && !layer.empty(); ++tau)
    {
        next.clear();
        for(const auto& entry : layer)
        {
            const int costSoFar = entry.second;
            const St st = decode(entry.first);
            bool planesDone = true;
            for(int code : st.plane) if(FLY(code) || LOC(code) != G) { planesDone = false; break; }
            if(st.delivered == in.t && planesDone)
            {
                auto it = bestTime.find(costSoFar);
                if(it == bestTime.end() || tau < it->second) bestTime[costSoFar] = tau;
                continue;
            }
            ++expanded;
            std::vector<int> chosen(in.p);
            std::vector<int> pax = st.pax;
            auto finish = [&](int addedCost)
            {
                const int c = costSoFar + addedCost;
                if(c > costCap) return;
                St nx; nx.plane.resize(in.p); nx.pax = pax; nx.delivered = st.delivered;
                for(int k = 0; k < in.p; ++k)
                {
                    int code = chosen[k];
                    if(FLY(code))
                    {
                        const int dest = LOC(code), rem = REM(code), carry = CAR(code);
                        if(rem == 1)
                        {
                            if(carry) { if(dest == G) ++nx.delivered; else ++nx.pax[dest]; }
                            if(dest == 0 || dest == G) code = mk(dest, 0, 0, dest == G, 0, 0);
                            else code = mk(dest, 0, 0, STA(code), SEGM(code), 0);
                            code &= ~dropMask;   // forget what the class does not look at
                        }
                        else code = mk(dest, 1, carry, STA(code), SEGM(code), rem - 1);
                        code &= ~dropMask;
                    }
                    nx.plane[k] = code;
                }
                std::sort(nx.plane.begin(), nx.plane.end());
                const Key key = encode(nx);
                auto it = seen.find(key);
                if(it != seen.end() && it->second <= c) return;
                seen[key] = c;
                auto jt = next.find(key);
                if(jt == next.end() || c < jt->second) next[key] = c;
            };
            std::function<void(int, int)> choose = [&](int k, int addedCost)
            {
                if(k == in.p) { finish(addedCost); return; }
                const int code = st.plane[k];
                if(FLY(code)) { chosen[k] = code; choose(k + 1, addedCost); return; }
                chosen[k] = code; choose(k + 1, addedCost);   // wait one tick
                const int here = LOC(code);
                const bool atHub = (here == 0 || here == G);
                for(int dest = 0; dest <= G; ++dest)
                {
                    const int d = in.dur(here, dest);
                    if(d == 0) continue;
                    int sta, m;
                    if(atHub) { sta = (here == G); m = 1; }
                    else
                    {
                        sta = STA(code);
                        if(dest == 0 || dest == G) { if(SEGM(code) > allowM[sta][dest == G]) continue; m = SEGM(code); }
                        else { m = std::min(SEGM(code) + 1, UNB); if(m > maxStart[sta]) continue; }
                    }
                    const int land = (dest >= 1 && dest <= in.n) ? in.cost[dest - 1] : 0;
                    chosen[k] = mk(dest, 1, 0, sta, m, d); choose(k + 1, addedCost + land);
                    const bool centralLeg = !atHub && dest != 0 && dest != G;
                    if(here != G && pax[here] > 0 && !(centralLeg && emptyCentral[sta]))
                    {
                        --pax[here];
                        chosen[k] = mk(dest, 1, 1, sta, m, d); choose(k + 1, addedCost + land);
                        ++pax[here];
                    }
                }
            };
            choose(0, 0);
        }
        layer.swap(next);
    }
    int best = 1 << 30;
    for(const auto& kv : bestTime) if(kv.second < best) { std::printf("%d %d\n", kv.first, kv.second); best = kv.second; }
    std::fprintf(stderr, "states expanded: %ld, cost cap %d, time cap %d\n", expanded, costCap, timeCap);
    return 0;
}
