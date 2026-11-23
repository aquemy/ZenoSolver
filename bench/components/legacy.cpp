// Components of the 2016 solver. They are the reference for the new library's
// benchmarks and are removed together with the legacy solvers.
#include <paretoExtraction.hpp>

#include <zs_bench.hpp>

#include <map>
#include <random>

namespace
{
// Pareto extraction from a map cost -> makespan of `size` random points.
void BM_LegacyParetoExtraction(benchmark::State& state)
{
    const auto size = static_cast<int>(state.range(0));
    std::mt19937 rng(42);
    std::uniform_int_distribution<int> value(0, 100 * size);
    std::map<int, int> points;
    while(static_cast<int>(points.size()) < size)
        points[value(rng)] = value(rng);

    std::size_t frontSize = 0;
    for(auto _ : state)
    {
        auto copy = points;
        auto front = paretoExtraction(copy);
        frontSize = front.size();
        benchmark::DoNotOptimize(front);
    }
    state.counters["front_size"] = static_cast<double>(frontSize);
    state.SetComplexityN(size);
    zs::bench::reportPeakRss(state);
}
BENCHMARK(BM_LegacyParetoExtraction)->RangeMultiplier(4)->Range(16, 1 << 16)->Complexity();
} // namespace
