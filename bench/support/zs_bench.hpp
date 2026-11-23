// Helpers shared by the component benchmarks.
#pragma once

#include <benchmark/benchmark.h>

#include <cstdint>
#include <sys/resource.h>

namespace zs::bench
{
/// Peak resident set size of the process, in bytes.
inline std::uint64_t peakRssBytes()
{
    rusage usage{};
    getrusage(RUSAGE_SELF, &usage);
#if defined(__APPLE__)
    return static_cast<std::uint64_t>(usage.ru_maxrss); // bytes on macOS
#else
    return static_cast<std::uint64_t>(usage.ru_maxrss) * 1024; // kilobytes on Linux
#endif
}

/// Adds the process peak RSS (MiB) to a benchmark's counters. Peak RSS is
/// monotone over the process, so run memory-sensitive benchmarks with
/// --benchmark_filter on their own when the absolute value matters.
inline void reportPeakRss(benchmark::State& state)
{
    state.counters["peak_rss_mib"] = benchmark::Counter(static_cast<double>(peakRssBytes()) / (1024.0 * 1024.0));
}

/// A counter averaged over iterations (states visited, pruned, ...).
inline benchmark::Counter perIteration(double total)
{
    return benchmark::Counter(total, benchmark::Counter::kAvgIterations);
}
} // namespace zs::bench
