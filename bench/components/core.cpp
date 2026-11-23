// Component benchmarks of the exact solver (zeno_core).
//
//   bm-core --benchmark_filter=OnePlane    one-plane table G
//   bm-core --benchmark_filter=Relaxed     lower bound L at one level
//   bm-core --benchmark_filter=Forest      U (2), U3 (3) and the exact DP at one level
//   bm-core --benchmark_filter=Solve       end-to-end front
//
// Instances come from the 2016 generator (zeno::legacy), so they match the
// suites in bench/instances. The complexity fits are against the bounds of
// doc/theory/exact-front.md: G in O(n * m * T), L in O(p * s^2) per level,
// the forest DP in O(K * n * q^2 * s^2) per level, K the size of the
// children staircases (q = trees' planes).
#include <zeno/forest.hpp>
#include <zeno/legacy_input.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/reduce.hpp>
#include <zeno/solve.hpp>

#include <zs_bench.hpp>

#include <random>

namespace
{
zeno::Instance generated(int n, int t, int p, int costFunction = 3, int durationFunction = 3, int adjust = 1)
{
    zeno::legacy::Options o;
    o.n = n;
    o.t = t;
    o.p = p;
    o.costFunction = costFunction;
    o.durationFunction = durationFunction;
    o.adjust = adjust;
    return zeno::legacy::buildInstance(o);
}

/// Random symmetric instance with durations in [1, maxDuration].
zeno::Instance randomInstance(int n, int t, int p, int maxDuration, unsigned seed)
{
    std::mt19937 rng(seed);
    std::uniform_int_distribution<int> dur(1, maxDuration), cost(1, 100);
    zeno::Instance in;
    for(int i = 0; i < n; ++i)
    {
        in.d.push_back(dur(rng));
        in.c.push_back(cost(rng));
    }
    in.dbar = in.d;
    in.t = t;
    in.p = p;
    return in;
}

// G over (n, D): n cities with durations up to D = range(1); dense (range(2)
// = 0) or staircase (1).
void BM_OnePlaneTable(benchmark::State& state)
{
    const auto n = static_cast<int>(state.range(0));
    const auto D = static_cast<int>(state.range(1));
    const auto layout = state.range(2) == 0 ? zeno::OnePlaneTable::Layout::Dense : zeno::OnePlaneTable::Layout::Staircase;
    const auto in = randomInstance(n, 20, 4, D, 1);
    const auto r = zeno::reduce(in);
    const zeno::Time maxT = r.highestLevel();
    std::size_t entries = 0;
    for(auto _ : state)
    {
        zeno::OnePlaneTable G(r.d, r.c, r.maxGroup(), maxT, layout);
        benchmark::DoNotOptimize(G(r.maxGroup(), maxT));
        entries = G.size();
    }
    state.counters["cities"] = r.n();
    state.counters["entries"] = static_cast<double>(entries);
    state.counters["cells"] = static_cast<double>(r.maxGroup() + 1) * static_cast<double>(maxT + 1);
    zs::bench::reportPeakRss(state);
}
BENCHMARK(BM_OnePlaneTable)->ArgsProduct({{10, 40, 160}, {10, 100, 1000}, {0, 1}});

// L at the middle level of the default generator, sweeping t (s = 2t - p).
void BM_RelaxedLevel(benchmark::State& state)
{
    const auto t = static_cast<int>(state.range(0));
    const auto r = zeno::reduce(generated(20, t, 5));
    const zeno::OnePlaneTable G(r.d, r.c, r.maxGroup(), r.highestLevel());
    const zeno::Time T = (r.lowestLevel() + r.highestLevel()) / 2;
    zeno::LevelStats work;
    for(auto _ : state)
        benchmark::DoNotOptimize(zeno::relaxedCost(r, G, T, &work));
    state.counters["relaxations"] = zs::bench::perIteration(static_cast<double>(work.relaxations));
    state.SetComplexityN(static_cast<benchmark::IterationCount>(r.p) * r.landings() * r.landings());
}
BENCHMARK(BM_RelaxedLevel)->RangeMultiplier(2)->Range(8, 128)->Complexity(benchmark::oN);

// forestCost at one level with trees of at most range(1) planes.
void BM_ForestLevel(benchmark::State& state)
{
    const auto t = static_cast<int>(state.range(0));
    const auto q = static_cast<int>(state.range(1));
    const auto in = randomInstance(12, t, 6, 30, 3);
    const auto r = zeno::reduce(in);
    const zeno::OnePlaneTable G(r.d, r.c, r.maxGroup(), r.highestLevel());
    const zeno::Time T = (r.lowestLevel() + r.highestLevel()) / 2;
    zeno::LevelStats work;
    for(auto _ : state)
        benchmark::DoNotOptimize(zeno::forestCost(r, G, T, q, &work));
    state.counters["level"] = static_cast<double>(T);
    state.counters["maxTree"] = std::min(q, r.maxTree());
    state.counters["states"] = zs::bench::perIteration(static_cast<double>(work.states));
    state.counters["relaxations"] = zs::bench::perIteration(static_cast<double>(work.relaxations));
    zs::bench::reportPeakRss(state);
}
BENCHMARK(BM_ForestLevel)->ArgsProduct({{8, 12, 16}, {2, 3, 6}})->Unit(benchmark::kMillisecond);

// End to end on the suites' regimes and families.
void BM_SolveGenerated(benchmark::State& state)
{
    const auto n = static_cast<int>(state.range(0));
    const auto t = static_cast<int>(state.range(1));
    const auto p = static_cast<int>(state.range(2));
    const auto family = static_cast<int>(state.range(3));
    const auto in = generated(n, t, p, family, family, family == 3 ? 1 : 100);
    zeno::SolveResult result;
    for(auto _ : state)
        result = zeno::solveFront(in);
    state.counters["front_size"] = static_cast<double>(result.front.size());
    state.counters["levels"] = static_cast<double>(result.stats.levels);
    state.counters["exact_calls"] = static_cast<double>(result.stats.exactCalls);
    state.counters["open_after_bracket"] = static_cast<double>(result.stats.levels - result.stats.closedByBracket - result.stats.closedByPairs);
    zs::bench::reportPeakRss(state);
}
BENCHMARK(BM_SolveGenerated)
    ->Args({200, 3, 2, 3})
    ->Args({20, 6, 2, 3})
    ->Args({8, 26, 25, 3})
    ->Args({50, 30, 5, 3})
    ->Args({100, 60, 10, 3})
    ->Args({10, 8, 3, 1})
    ->Args({10, 8, 3, 2})
    ->Unit(benchmark::kMillisecond);

// End to end with large durations (sqrt family scaled by range(0)): the
// level range grows linearly, the breakpoint search and the staircases keep
// time and memory flat.
void BM_SolveLargeDurations(benchmark::State& state)
{
    const auto in = generated(10, 8, 3, 2, 2, static_cast<int>(state.range(0)));
    zeno::SolveResult result;
    for(auto _ : state)
        result = zeno::solveFront(in);
    state.counters["levels"] = static_cast<double>(result.stats.levels);
    state.counters["front_size"] = static_cast<double>(result.front.size());
    state.counters["evaluations"] = static_cast<double>(result.stats.closedByBracket + result.stats.closedByPairs + result.stats.closedByChains + result.stats.exactCalls);
    zs::bench::reportPeakRss(state);
}
BENCHMARK(BM_SolveLargeDurations)->RangeMultiplier(10)->Range(100, 10000000)->Unit(benchmark::kMillisecond);

// End to end on random instances, where the exact DP runs on open levels.
void BM_SolveRandom(benchmark::State& state)
{
    const auto t = static_cast<int>(state.range(0));
    const auto p = static_cast<int>(state.range(1));
    const auto in = randomInstance(10, t, p, 60, 11);
    zeno::SolveResult result;
    for(auto _ : state)
        result = zeno::solveFront(in);
    state.counters["front_size"] = static_cast<double>(result.front.size());
    state.counters["exact_calls"] = static_cast<double>(result.stats.exactCalls);
    zs::bench::reportPeakRss(state);
}
BENCHMARK(BM_SolveRandom)->ArgsProduct({{10, 14, 18}, {4, 6}})->Unit(benchmark::kMillisecond);
} // namespace
