// Component benchmarks of the non-symmetric bracket.
//
//   bm-ns --benchmark_filter=Bracket     solveBracket end to end
//   bm-ns --benchmark_filter=Lagrangian  the Lagrangian balance bound at one level
//   bm-ns --benchmark_filter=Balanced    the exact balanced role program at one level
//   bm-ns --benchmark_filter=Schedule    scheduling a balanced configuration
#include <zeno/legacy_input.hpp>
#include <zeno/ns.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/reduce.hpp>
#include <zeno/roles.hpp>

#include <zs_bench.hpp>

#include <random>

namespace
{
zeno::Instance randomNonSymmetric(int n, int t, int p, unsigned seed)
{
    std::mt19937 rng(seed);
    std::uniform_int_distribution<int> value(1, 30), cost(1, 50);
    zeno::Instance in;
    for(int i = 0; i < n; ++i)
    {
        in.d.push_back(value(rng));
        in.dbar.push_back(value(rng));
        in.c.push_back(cost(rng));
    }
    in.t = t;
    in.p = p;
    return in;
}

// End to end, with t - p (the number of links) swept.
void BM_Bracket(benchmark::State& state)
{
    const auto in = randomNonSymmetric(static_cast<int>(state.range(0)), static_cast<int>(state.range(1)), 3, 7);
    zeno::BracketResult result;
    for(auto _ : state)
        result = zeno::solveBracket(in);
    std::size_t open = 0;
    for(auto g : result.gapProof)
        open += g == zeno::GapProof::Open;
    state.counters["points"] = static_cast<double>(result.upper.size());
    state.counters["open_gaps"] = static_cast<double>(open);
    state.counters["exact"] = result.exact() ? 1 : 0;
    state.counters["evaluations"] = static_cast<double>(result.stats.exactCalls);
    zs::bench::reportPeakRss(state);
}
BENCHMARK(BM_Bracket)->ArgsProduct({{3, 6}, {5, 6, 7}})->Unit(benchmark::kMillisecond);

struct Level
{
    zeno::ReducedInstance r;
    zeno::OnePlaneTable fill;
    zeno::Time T;
    explicit Level(const zeno::Instance& in)
        : r(zeno::reduce(in))
        , fill(r.fill, r.c, r.maxGroup(), r.highestLevel())
        , T((r.lowestLevel() + r.highestLevel()) / 2) {}
};

void BM_Lagrangian(benchmark::State& state)
{
    const Level level(randomNonSymmetric(static_cast<int>(state.range(0)), static_cast<int>(state.range(1)), 3, 11));
    for(auto _ : state)
        benchmark::DoNotOptimize(zeno::lagrangianRoles(level.r, level.T, zeno::kInfCost, 20));
    state.counters["level"] = static_cast<double>(level.T);
}
BENCHMARK(BM_Lagrangian)->ArgsProduct({{3, 6, 12}, {6, 8}})->Unit(benchmark::kMillisecond);

void BM_Balanced(benchmark::State& state)
{
    const Level level(randomNonSymmetric(static_cast<int>(state.range(0)), static_cast<int>(state.range(1)), 3, 11));
    bool complete = false;
    for(auto _ : state)
    {
        const zeno::BalancedRoles program(level.r, level.fill, level.T);
        complete = program.complete();
        benchmark::DoNotOptimize(program.value());
    }
    state.counters["complete"] = complete ? 1 : 0;
    state.counters["links"] = state.range(1) - 3;
}
BENCHMARK(BM_Balanced)->ArgsProduct({{3, 6}, {5, 6, 7}})->Unit(benchmark::kMillisecond);

void BM_Schedule(benchmark::State& state)
{
    const auto in = randomNonSymmetric(4, static_cast<int>(state.range(0)), 3, 13);
    const Level level(in);
    const zeno::BalancedRoles program(level.r, level.fill, level.r.highestLevel());
    if(!program.optimal())
    {
        state.SkipWithError("no balanced configuration");
        return;
    }
    const auto config = program.reconstruct();
    for(auto _ : state)
        benchmark::DoNotOptimize(zeno::scheduleRoles(in, level.r, config).has_value());
}
BENCHMARK(BM_Schedule)->DenseRange(5, 8)->Unit(benchmark::kMicrosecond);
} // namespace
