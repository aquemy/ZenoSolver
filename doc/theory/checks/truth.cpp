// Ground truth for tiny MultiZenoTravel instances: exhaustive search of the
// real planning problem. It assumes NOTHING from the papers (no 2t-p landings,
// no patterns, no "planes end in C_G").
//
// Model: cities I (0), central 1..n, G (n+1). Flights I<->c_i (west[i]),
// c_i<->G (east[i]), c_i<->c_j (D[i][j], optional). No direct I-G flight.
// p planes start in I, capacity one passenger; t passengers start in I and must
// reach G. Landing in central city i costs c[i]. Boarding and leaving a plane
// take no time; planes and passengers may wait anywhere. Integer durations.
// Objectives: total landing cost, and the time the last passenger reaches G.
//
// Search: breadth-first over time (one tick per layer). A state reached again
// later with a cost that is not lower is dropped (waiting is allowed, so the
// earlier, cheaper visit dominates).
//
// usage: truth <west> <east> <cost> <t> <p> <central: none | a1 | tight> [extraLandings]
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

struct Inst
{
    int n = 0, t = 0, p = 0;
    std::vector<int> west, east, cost;
    std::vector<std::vector<int>> D;   // 0 = no flight between these central cities
    int dur(int a, int b) const        // 0 = no flight
    {
        if(a == b) return 0;
        if(a > b) std::swap(a, b);
        if(a == 0 && b == n + 1) return 0;
        if(a == 0) return west[b - 1];
        if(b == n + 1) return east[a - 1];
        return D[a - 1][b - 1];
    }
};

static int RMAX = 1;
struct State
{
    std::vector<int> plane;   // code per plane, sorted
    std::vector<int> pax;     // passengers waiting at I and at each central city
    int delivered = 0;
};
static uint64_t encode(const State& s)
{
    uint64_t k = 0;
    for(int c : s.plane) k = (k << 8) | (uint64_t)c;
    for(int c : s.pax) k = (k << 3) | (uint64_t)c;
    return (k << 3) | (uint64_t)s.delivered;
}
static State decode(uint64_t k, const Inst& in)
{
    State s; s.delivered = (int)(k & 7); k >>= 3;
    s.pax.assign(in.n + 1, 0);
    for(int i = in.n; i >= 0; --i) { s.pax[i] = (int)(k & 7); k >>= 3; }
    s.plane.assign(in.p, 0);
    for(int i = in.p - 1; i >= 0; --i) { s.plane[i] = (int)(k & 255); k >>= 8; }
    return s;
}
// Plane codes: idle at location L -> L. Flying to dest, rem ticks left, carrying or not.
static int flying(const Inst& in, int dest, int rem, int carry) { return (in.n + 2) + ((dest * RMAX + (rem - 1)) * 2 + carry); }
static bool isIdle(const Inst& in, int code) { return code < in.n + 2; }

int main(int argc, char** argv)
{
    if(argc < 7) { std::fprintf(stderr, "usage: truth west east cost t p none|a1|tight [extraLandings]\n"); return 2; }
    auto parse = [](const char* s) { std::vector<int> v; const char* q = s; while(*q) { v.push_back(std::atoi(q)); while(*q && *q != ',') ++q; if(*q) ++q; } return v; };
    Inst in; in.west = parse(argv[1]); in.east = parse(argv[2]); in.cost = parse(argv[3]);
    in.t = std::atoi(argv[4]); in.p = std::atoi(argv[5]); in.n = (int)in.west.size();
    const std::string central = argv[6];
    const int extra = argc > 7 ? std::atoi(argv[7]) : 2;
    in.D.assign(in.n, std::vector<int>(in.n, 0));
    for(int i = 0; i < in.n; ++i) for(int j = 0; j < in.n; ++j) if(i != j)
    {
        if(central == "a1")    // strictly longer than going through I or through G
            in.D[i][j] = std::max(in.west[i] + in.west[j], in.east[i] + in.east[j]) + 1;
        else if(central == "tight")   // smallest value satisfying the triangle inequalities
            in.D[i][j] = std::max({std::abs(in.west[i] - in.west[j]), std::abs(in.east[i] - in.east[j]), 1});
    }
    for(int a = 0; a <= in.n + 1; ++a) for(int b = 0; b <= in.n + 1; ++b) RMAX = std::max(RMAX, in.dur(a, b));
    if((in.n + 2) + (in.n + 2) * RMAX * 2 > 255 || in.t > 7 || in.p > 4 || in.n > 4) { std::fprintf(stderr, "instance too large for the state encoding\n"); return 2; }

    const int s = 2 * in.t - in.p;
    const int cmax = *std::max_element(in.cost.begin(), in.cost.end());
    const int costCap = (s + extra) * cmax;                 // lets plans use extra landings
    int slowest = 0; for(int i = 0; i < in.n; ++i) slowest = std::max(slowest, in.west[i] + in.east[i]);
    const int timeCap = s * slowest;                        // sequential plan through the slowest city

    State start; start.plane.assign(in.p, 0); start.pax.assign(in.n + 1, 0); start.pax[0] = in.t;
    std::unordered_map<uint64_t, int> seen, layer, next;
    layer[encode(start)] = 0; seen[encode(start)] = 0;
    std::map<int, int> bestTime;   // cost -> earliest completion
    long expanded = 0;

    for(int tau = 0; tau <= timeCap && !layer.empty(); ++tau)
    {
        next.clear();
        for(const auto& entry : layer)
        {
            const int costSoFar = entry.second;
            const State st = decode(entry.first, in);
            // Planes must end in C_G (set ANYWHERE=1 for the former, looser model).
            bool planesDone = true;
            if(!std::getenv("ANYWHERE"))
                for(int code : st.plane) if(code != in.n + 1) { planesDone = false; break; }
            if(st.delivered == in.t && planesDone)
            {
                auto it = bestTime.find(costSoFar);
                if(it == bestTime.end() || tau < it->second) bestTime[costSoFar] = tau;
                continue;
            }
            ++expanded;
            // Joint choice for the idle planes, one plane at a time.
            std::vector<int> chosen(in.p);
            std::vector<int> pax = st.pax;
            auto finish = [&](int addedCost)
            {
                const int c = costSoFar + addedCost;
                if(c > costCap) return;
                State nx; nx.plane.resize(in.p); nx.pax = pax; nx.delivered = st.delivered;
                for(int k = 0; k < in.p; ++k)
                {
                    int code = chosen[k];
                    if(!isIdle(in, code))
                    {
                        int v = code - (in.n + 2); const int carry = v & 1; v >>= 1;
                        const int dest = v / RMAX, rem = v % RMAX + 1;
                        if(rem == 1)
                        {
                            code = dest;
                            if(carry) { if(dest == in.n + 1) ++nx.delivered; else ++nx.pax[dest]; }
                        }
                        else code = flying(in, dest, rem - 1, carry);
                    }
                    nx.plane[k] = code;
                }
                std::sort(nx.plane.begin(), nx.plane.end());
                const uint64_t key = encode(nx);
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
                if(!isIdle(in, code)) { chosen[k] = code; choose(k + 1, addedCost); return; }
                // Identical idle planes at the same place: impose an order on their choices.
                chosen[k] = code; choose(k + 1, addedCost);              // stay
                for(int dest = 0; dest <= in.n + 1; ++dest)
                {
                    const int d = in.dur(code, dest);
                    if(d == 0) continue;
                    const int land = (dest >= 1 && dest <= in.n) ? in.cost[dest - 1] : 0;
                    chosen[k] = flying(in, dest, d, 0); choose(k + 1, addedCost + land);
                    if(code != in.n + 1 && pax[code] > 0)                   // board a waiting passenger
                    {
                        --pax[code];
                        chosen[k] = flying(in, dest, d, 1); choose(k + 1, addedCost + land);
                        ++pax[code];
                    }
                }
            };
            choose(0, 0);
        }
        layer.swap(next);
    }
    int best = 1 << 30;
    for(const auto& kv : bestTime) if(kv.second < best) { std::printf("%d %d\n", kv.first, kv.second); best = kv.second; }
    std::fprintf(stderr, "states expanded: %ld, cost cap %d (2t-p+%d landings of the dearest city), time cap %d\n", expanded, costCap, extra, timeCap);
    return 0;
}
