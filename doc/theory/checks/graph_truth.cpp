// Ground truth for tiny MultiZenoTravel instances on an arbitrary flight graph
// (arXiv 2304.14659 §2.4): exhaustive search of the planning problem, written
// after truth.cpp but with no clique structure.
//
// Model: vertices I (0), central 1..n, G (n+1); any set of undirected edges
// with integer durations >= 1, except an edge I-G. p planes start in I,
// capacity one passenger; t passengers start in I and must reach G. Every
// arrival in central vertex i costs c[i]; hubs are free. Passengers may change
// planes at any vertex, planes and passengers may wait anywhere, routes are
// arbitrary walks. Planes end in G (ANYWHERE=1: planes end anywhere, the
// makespan is then the last arrival). Objectives: total landing cost and
// makespan.
//
// Search: breadth-first over time (one tick per layer) on states made of the
// plane positions (idle at a vertex, or flying to a vertex with some ticks
// left, carrying a passenger or not) and the number of passengers waiting at
// each vertex. A state reached again later with a cost that is not lower is
// dropped: waiting is allowed and the future depends on the state only, so the
// earlier visit dominates. Every plan with makespan <= timeCap is explored, so
// the output is the exact front of the plans with makespan <= timeCap.
//
// usage: graph_truth <edges> <costs> <t> <p> <timeCap>
//   edges: comma-separated u-v:duration with u, v in I, G, 1..n, e.g. I-1:1,1-2:2,2-G:1
//   costs: c_1,...,c_n
// output: the front, one "cost makespan" line per point by increasing cost.
#include <algorithm>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <functional>
#include <map>
#include <string>
#include <unordered_map>
#include <vector>

using Key = unsigned __int128;
struct KeyHash
{
    std::size_t operator()(Key k) const
    {
        const uint64_t lo = (uint64_t)k, hi = (uint64_t)(k >> 64);
        return std::hash<uint64_t>()(lo ^ (hi * 0x9E3779B97F4A7C15ull));
    }
};

struct Inst
{
    int n = 0, t = 0, p = 0;
    std::vector<int> cost;                // per vertex, 0 for the hubs
    std::vector<std::vector<int>> D;      // 0 = no edge
};

static int RMAX = 1;
static int BITS_PLANE = 16;
struct State
{
    std::vector<int> plane;   // code per plane, sorted
    std::vector<int> pax;     // passengers waiting at I and at each central vertex
    int delivered = 0;
};
static Key encode(const State& s)
{
    Key k = 0;
    for(int c : s.plane) k = (k << BITS_PLANE) | (Key)c;
    for(int c : s.pax) k = (k << 3) | (Key)c;
    return (k << 3) | (Key)s.delivered;
}
static State decode(Key k, const Inst& in)
{
    State s; s.delivered = (int)(k & 7); k >>= 3;
    s.pax.assign(in.n + 1, 0);
    for(int i = in.n; i >= 0; --i) { s.pax[i] = (int)(k & 7); k >>= 3; }
    s.plane.assign(in.p, 0);
    for(int i = in.p - 1; i >= 0; --i) { s.plane[i] = (int)(k & ((1u << BITS_PLANE) - 1)); k >>= BITS_PLANE; }
    return s;
}
// Plane codes: idle at vertex L -> L. Flying to dest, rem ticks left, carrying or not.
static int flying(const Inst& in, int dest, int rem, int carry) { return (in.n + 2) + ((dest * RMAX + (rem - 1)) * 2 + carry); }
static bool isIdle(const Inst& in, int code) { return code < in.n + 2; }

static int vertex(const std::string& s, int n)
{
    if(s == "I") return 0;
    if(s == "G") return n + 1;
    return std::atoi(s.c_str());
}

int main(int argc, char** argv)
{
    if(argc < 6) { std::fprintf(stderr, "usage: graph_truth edges costs t p timeCap\n"); return 2; }
    Inst in;
    {
        const char* q = argv[2];
        while(*q) { in.cost.push_back(std::atoi(q)); while(*q && *q != ',') ++q; if(*q) ++q; }
    }
    in.n = (int)in.cost.size();
    in.cost.insert(in.cost.begin(), 0);
    in.cost.push_back(0);
    in.t = std::atoi(argv[3]); in.p = std::atoi(argv[4]);
    const int timeCap = std::atoi(argv[5]);
    in.D.assign(in.n + 2, std::vector<int>(in.n + 2, 0));
    {
        std::string edges = argv[1];
        std::size_t pos = 0;
        while(pos < edges.size())
        {
            std::size_t comma = edges.find(',', pos);
            if(comma == std::string::npos) comma = edges.size();
            const std::string item = edges.substr(pos, comma - pos);
            const std::size_t dash = item.find('-'), colon = item.find(':');
            const int u = vertex(item.substr(0, dash), in.n), v = vertex(item.substr(dash + 1, colon - dash - 1), in.n);
            const int d = std::atoi(item.substr(colon + 1).c_str());
            if(u < 0 || v < 0 || u > in.n + 1 || v > in.n + 1 || u == v || d < 1 || (std::min(u, v) == 0 && std::max(u, v) == in.n + 1))
            { std::fprintf(stderr, "bad edge %s\n", item.c_str()); return 2; }
            in.D[u][v] = in.D[v][u] = d;
            RMAX = std::max(RMAX, d);
            pos = comma + 1;
        }
    }
    const int maxCode = (in.n + 2) + 2 * (in.n + 2) * RMAX;
    if(maxCode >= (1 << BITS_PLANE) || in.t > 7 || in.p > 4 || in.p > in.t || in.p < 1
       || BITS_PLANE * in.p + 3 * (in.n + 2) > 128)
    { std::fprintf(stderr, "instance too large for the state encoding\n"); return 2; }

    const bool anywhere = std::getenv("ANYWHERE") != nullptr;
    State start; start.plane.assign(in.p, 0); start.pax.assign(in.n + 1, 0); start.pax[0] = in.t;
    std::unordered_map<Key, int, KeyHash> seen, layer, next;
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
            bool planesDone = true;
            for(int code : st.plane)
                if(anywhere ? !isIdle(in, code) : code != in.n + 1) { planesDone = false; break; }
            if(st.delivered == in.t && planesDone)
            {
                auto it = bestTime.find(costSoFar);
                if(it == bestTime.end() || tau < it->second) bestTime[costSoFar] = tau;
                continue;
            }
            if(tau == timeCap) continue;
            ++expanded;
            std::vector<int> chosen(in.p);
            std::vector<int> pax = st.pax;
            auto finish = [&](int addedCost)
            {
                const int c = costSoFar + addedCost;
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
                if(!isIdle(in, code)) { chosen[k] = code; choose(k + 1, addedCost); return; }
                chosen[k] = code; choose(k + 1, addedCost);              // stay one tick
                for(int dest = 0; dest <= in.n + 1; ++dest)
                {
                    const int d = in.D[code][dest];
                    if(d == 0) continue;
                    const int land = in.cost[dest];
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
    std::fprintf(stderr, "states expanded: %ld, time cap %d%s\n", expanded, timeCap, anywhere ? ", planes end anywhere" : "");
    return 0;
}
