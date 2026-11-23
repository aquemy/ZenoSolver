#pragma once

#include <algorithm>
#include <atomic>
#include <cstddef>
#include <exception>
#include <mutex>
#include <thread>
#include <vector>

namespace zeno
{
/// Number of worker threads for `requested` (0 = hardware concurrency).
[[nodiscard]] inline unsigned workerCount(unsigned requested) noexcept
{
    const unsigned hardware = std::max(1u, std::thread::hardware_concurrency());
    return requested == 0 ? hardware : requested;
}

/// Calls body(i) for every i in [0, count), on up to `threads` threads (0 =
/// hardware concurrency), with dynamic scheduling. Rethrows the first exception.
template<class Body>
void parallelFor(std::size_t count, unsigned threads, Body&& body)
{
    const auto workers = static_cast<std::size_t>(std::min<std::size_t>(workerCount(threads), count));
    if(workers <= 1)
    {
        for(std::size_t i = 0; i < count; ++i)
            body(i);
        return;
    }
    std::atomic<std::size_t> next{0};
    std::exception_ptr error;
    std::mutex errorMutex;
    {
        std::vector<std::jthread> pool;
        pool.reserve(workers);
        for(std::size_t w = 0; w < workers; ++w)
            pool.emplace_back([&] {
                for(std::size_t i = next++; i < count; i = next++)
                {
                    try
                    {
                        body(i);
                    }
                    catch(...)
                    {
                        const std::scoped_lock lock(errorMutex);
                        if(!error)
                            error = std::current_exception();
                        next = count;
                    }
                }
            });
    }
    if(error)
        std::rethrow_exception(error);
}
} // namespace zeno
