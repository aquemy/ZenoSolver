// Component benchmarks around the front: reduction, plans, certificates, I/O.
//
//   bm-plan --benchmark_filter=Reduce       dominance reduction
//   bm-plan --benchmark_filter=Plan         buildPlan and checkPlan per front point
//   bm-plan --benchmark_filter=Certificate  make, write, read and check a certificate
//   bm-plan --benchmark_filter=Io           PDDL and data-file writers, the instance builder
#include <zeno/certificate.hpp>
#include <zeno/io.hpp>
#include <zeno/legacy_input.hpp>
#include <zeno/reduce.hpp>
#include <zeno/solve.hpp>

#include <zs_bench.hpp>

#include <random>
#include <sstream>

namespace
{
zeno::Instance generated(int n, int t, int p)
{
    zeno::legacy::Options o;
    o.n = n;
    o.t = t;
    o.p = p;
    return zeno::legacy::buildInstance(o);
}

zeno::Instance randomInstance(int n, int t, int p, unsigned seed)
{
    std::mt19937 rng(seed);
    std::uniform_int_distribution<int> value(1, 1000);
    zeno::Instance in;
    for(int i = 0; i < n; ++i)
    {
        in.d.push_back(value(rng));
        in.c.push_back(value(rng));
    }
    in.dbar = in.d;
    in.t = t;
    in.p = p;
    return in;
}

// Dominance reduction over n random cities (O(n * kept)).
void BM_Reduce(benchmark::State& state)
{
    const auto in = randomInstance(static_cast<int>(state.range(0)), 10, 3, 5);
    std::size_t kept = 0;
    for(auto _ : state)
    {
        const auto r = zeno::reduce(in);
        kept = r.d.size();
        benchmark::DoNotOptimize(kept);
    }
    state.counters["kept"] = static_cast<double>(kept);
    state.SetComplexityN(state.range(0));
}
BENCHMARK(BM_Reduce)->RangeMultiplier(4)->Range(16, 16384)->Complexity(benchmark::oNLogN);

// Plans of every front point: building (reconstruction excluded) and simulating.
void BM_PlanBuildAndCheck(benchmark::State& state)
{
    const auto t = static_cast<int>(state.range(0));
    const auto in = generated(20, t, 4);
    zeno::SolveOptions options;
    options.plans = true;
    const auto result = zeno::solveFront(in, options);
    std::size_t legs = 0;
    for(auto _ : state)
        for(const auto& plan : result.plans)
        {
            auto makespan = zeno::checkPlan(in, plan).makespan;
            benchmark::DoNotOptimize(makespan);
        }
    for(const auto& plan : result.plans)
        for(const auto& plane : plan.planes)
            legs += plane.size();
    state.counters["points"] = static_cast<double>(result.plans.size());
    state.counters["legs"] = static_cast<double>(legs);
    state.SetComplexityN(static_cast<benchmark::IterationCount>(legs));
}
BENCHMARK(BM_PlanBuildAndCheck)->RangeMultiplier(2)->Range(8, 64)->Complexity()->Unit(benchmark::kMicrosecond);

// The solve with plans, against the solve alone: the cost of reconstruction.
void BM_SolveWithPlans(benchmark::State& state)
{
    const auto in = generated(20, static_cast<int>(state.range(0)), 4);
    zeno::SolveOptions options;
    options.plans = state.range(1) != 0;
    for(auto _ : state)
        benchmark::DoNotOptimize(zeno::solveFront(in, options).front.size());
}
BENCHMARK(BM_SolveWithPlans)->ArgsProduct({{8, 16, 32}, {0, 1}})->Unit(benchmark::kMillisecond);

// Certificates: make (L at every gap), write, read and check.
void BM_Certificate(benchmark::State& state)
{
    const auto in = generated(20, static_cast<int>(state.range(0)), 4);
    zeno::SolveOptions options;
    options.plans = true;
    const auto result = zeno::solveFront(in, options);
    std::size_t bytes = 0;
    for(auto _ : state)
    {
        const auto cert = zeno::makeCertificate(in, result);
        std::stringstream text;
        zeno::writeCertificate(text, cert);
        bytes = text.str().size();
        const auto back = zeno::readCertificate(text);
        bool ok = zeno::checkCertificate(back).ok;
        benchmark::DoNotOptimize(ok);
    }
    state.counters["points"] = static_cast<double>(result.front.size());
    state.counters["certificate_bytes"] = static_cast<double>(bytes);
    zs::bench::reportPeakRss(state);
}
BENCHMARK(BM_Certificate)->RangeMultiplier(2)->Range(8, 64)->Unit(benchmark::kMillisecond);

// I/O: the instance builder, the PDDL writer and the data-file writer.
void BM_IoPddl(benchmark::State& state)
{
    const auto in = generated(static_cast<int>(state.range(0)), 20, 4);
    std::size_t bytes = 0;
    for(auto _ : state)
    {
        std::ostringstream out;
        zeno::writePddlProblem(out, in);
        bytes = out.str().size();
    }
    state.counters["bytes"] = static_cast<double>(bytes);
    state.SetComplexityN(state.range(0));
}
BENCHMARK(BM_IoPddl)->RangeMultiplier(4)->Range(4, 256)->Complexity(benchmark::oNSquared);

void BM_IoBuildInstance(benchmark::State& state)
{
    zeno::legacy::Options o;
    o.n = static_cast<int>(state.range(0));
    o.t = 20;
    o.p = 4;
    o.costFunction = 2;
    o.durationFunction = 2;
    o.adjust = 100;
    for(auto _ : state)
        benchmark::DoNotOptimize(zeno::legacy::buildInstance(o).d.size());
    state.SetComplexityN(state.range(0));
}
BENCHMARK(BM_IoBuildInstance)->RangeMultiplier(4)->Range(4, 4096)->Complexity();
} // namespace
