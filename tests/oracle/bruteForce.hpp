#ifndef _ZS_ORACLE_BRUTE_FORCE_
#define _ZS_ORACLE_BRUTE_FORCE_

////////////////////////////////////////////////////////////
/// \file bruteForce.hpp
/// \brief Exhaustive reference solver for tiny MultiZenoTravel
/// instances, used as a test oracle.
///
/// It shares no code with the solvers. Model (Quemy et al.,
/// "Pareto Fronts for MultiZenoTravel Benchmarks", 2014):
///
/// - Central cities 0..n-1; planes and travelers start at c_I.
/// - Flights only between c_I and c_i (duration west[i]) and
///   between c_i and c_G (duration east[i]). Landing in c_i
///   costs cost[i]; c_I and c_G are free.
/// - A Possibly Pareto-optimal Plan (PPP) is a multiset e of t
///   eastbound cities and a multiset w of t-p westbound cities.
///   Its cost is the sum of cost[] over e and w.
/// - Each plane performs a sequence of tasks:
///     East  (W -> E side, with a traveler)  west[i] + east[i]
///     West  (E -> W side, empty)            west[i] + east[i]
///     Open  (stay W, drop traveler at c_i)  2 * west[i]
///     Close (stay E, pick traveler at c_i)  2 * east[i]
///   Open/Close come in pairs (pattern P3) and consume one
///   element of e and one of w with the same city. A Close
///   cannot pick up before the matching Open drops; the
///   closing plane waits at c_i if needed.
///
/// For a PPP the oracle tries every P3 multiset (beta set),
/// every assignment of tasks to planes, every order, and every
/// matching of Opens to Closes, and simulates exact times. It
/// does not rely on the greedy algorithm or on its optimality.
/// It is exponential: keep instances tiny.
////////////////////////////////////////////////////////////

#include <algorithm>
#include <cstdint>
#include <functional>
#include <limits>
#include <map>
#include <optional>
#include <stdexcept>
#include <vector>

namespace oracle {

using Int = std::int64_t;
constexpr Int infinity = std::numeric_limits<Int>::max();

struct Instance
{
    std::vector<Int> cost;   ///< Landing cost of each central city.
    std::vector<Int> west;   ///< Duration c_I <-> c_i.
    std::vector<Int> east;   ///< Duration c_i <-> c_G.
    unsigned travelers = 0;  ///< t
    unsigned planes = 0;     ///< p
};

enum class Kind : std::uint8_t { East, West, Open, Close };

struct Task
{
    Kind kind;
    int city;
    int pair;  ///< Index of the P3 pair for Open/Close, -1 otherwise.
};

inline Int duration(const Instance& in, const Task& task)
{
    switch(task.kind)
    {
        case Kind::East:
        case Kind::West:  return in.west[task.city] + in.east[task.city];
        case Kind::Open:  return 2 * in.west[task.city];
        case Kind::Close: return 2 * in.east[task.city];
    }
    return 0;
}

////////////////////////////////////////////////////////////
/// \brief Exact makespan of fixed per-plane task sequences.
///
/// Every plane starts at c_I at time 0 and executes its
/// sequence without voluntary idling. A Close waits at its
/// city until the matching Open has dropped the traveler.
///
/// \return The makespan, or std::nullopt if the sequences
///         deadlock (a Close waits for an Open that can never
///         happen) or violate the side alternation.
////////////////////////////////////////////////////////////
inline std::optional<Int> simulate(const Instance& in,
    const std::vector<std::vector<Task>>& sequences,
    int pairs)
{
    // Static side check: W --East--> E --West--> W, Open on W, Close on E.
    for(const auto& sequence : sequences)
    {
        bool onWest = true;
        for(const auto& task : sequence)
        {
            switch(task.kind)
            {
                case Kind::East:  if(!onWest) return std::nullopt; onWest = false; break;
                case Kind::West:  if(onWest)  return std::nullopt; onWest = true;  break;
                case Kind::Open:  if(!onWest) return std::nullopt; break;
                case Kind::Close: if(onWest)  return std::nullopt; break;
            }
        }
    }

    const auto planes = sequences.size();
    std::vector<Int> time(planes, 0);
    std::vector<std::size_t> next(planes, 0);
    std::vector<std::optional<Int>> drop(pairs);

    bool progress = true;
    while(progress)
    {
        progress = false;
        for(std::size_t k = 0; k < planes; ++k)
        {
            while(next[k] < sequences[k].size())
            {
                const auto& task = sequences[k][next[k]];
                if(task.kind == Kind::Close)
                {
                    if(!drop[task.pair])
                        break;  // Blocked until the Open is simulated.
                    const Int arrival = time[k] + in.east[task.city];
                    time[k] = std::max(arrival, *drop[task.pair]) + in.east[task.city];
                }
                else if(task.kind == Kind::Open)
                {
                    drop[task.pair] = time[k] + in.west[task.city];
                    time[k] += 2 * in.west[task.city];
                }
                else
                {
                    time[k] += duration(in, task);
                }
                ++next[k];
                progress = true;
            }
        }
    }

    for(std::size_t k = 0; k < planes; ++k)
        if(next[k] != sequences[k].size())
            return std::nullopt;  // Deadlock.

    return *std::max_element(time.begin(), time.end());
}

////////////////////////////////////////////////////////////
/// \brief Exhaustive search of all schedules for a PPP and a
/// fixed beta set.
///
/// Planes are filled one after the other. Every plane must end
/// on the east side with exactly one more East than West task,
/// because |alpha_E| - |alpha_W| = p and each plane alternates
/// sides starting from the west.
////////////////////////////////////////////////////////////
class ScheduleSearch
{
public:
    ScheduleSearch(const Instance& in,
        const std::vector<int>& eastCount,
        const std::vector<int>& westCount,
        const std::vector<int>& betaCities)
        : in_(in)
        , eastLeft_(eastCount)
        , westLeft_(westCount)
        , pairCity_(betaCities)
        , opened_(betaCities.size(), false)
        , closed_(betaCities.size(), false)
        , sequences_(in.planes)
    {
    }

    /// \param bound Only schedules strictly better than bound are explored.
    Int run(Int bound)
    {
        best_ = bound;
        extend(0, true, 0);
        return best_;
    }

private:
    int total(const std::vector<int>& counts) const
    {
        int sum = 0;
        for(auto c : counts)
            sum += c;
        return sum;
    }

    bool allPairsDone() const
    {
        return std::all_of(opened_.begin(), opened_.end(), [](bool b) { return b; })
            && std::all_of(closed_.begin(), closed_.end(), [](bool b) { return b; });
    }

    void push(unsigned plane, Task task, bool onWest, Int load)
    {
        sequences_[plane].push_back(task);
        extend(plane, onWest, load + duration(in_, task));
        sequences_[plane].pop_back();
    }

    void extend(unsigned plane, bool onWest, Int load)
    {
        // Waiting can only add time, so the private load is a lower bound.
        if(load >= best_)
            return;

        if(onWest)
        {
            for(int city = 0; city < static_cast<int>(eastLeft_.size()); ++city)
            {
                if(eastLeft_[city] == 0)
                    continue;
                --eastLeft_[city];
                push(plane, Task{Kind::East, city, -1}, false, load);
                ++eastLeft_[city];
            }
            for(int pair = 0; pair < static_cast<int>(pairCity_.size()); ++pair)
            {
                if(opened_[pair])
                    continue;
                opened_[pair] = true;
                push(plane, Task{Kind::Open, pairCity_[pair], pair}, true, load);
                opened_[pair] = false;
            }
            return;
        }

        for(int city = 0; city < static_cast<int>(westLeft_.size()); ++city)
        {
            if(westLeft_[city] == 0)
                continue;
            --westLeft_[city];
            push(plane, Task{Kind::West, city, -1}, true, load);
            ++westLeft_[city];
        }
        for(int pair = 0; pair < static_cast<int>(pairCity_.size()); ++pair)
        {
            if(closed_[pair])
                continue;
            closed_[pair] = true;
            push(plane, Task{Kind::Close, pairCity_[pair], pair}, false, load);
            closed_[pair] = false;
        }

        // Close this plane (it is on the east side).
        const int planesLeft = static_cast<int>(in_.planes) - static_cast<int>(plane) - 1;
        if(total(eastLeft_) - total(westLeft_) != planesLeft)
            return;  // The remaining planes could not all end on the east side.
        if(planesLeft > 0)
        {
            extend(plane + 1, true, 0);
            return;
        }
        if(total(eastLeft_) != 0 || total(westLeft_) != 0 || !allPairsDone())
            return;
        if(auto makespan = simulate(in_, sequences_, static_cast<int>(pairCity_.size())))
            best_ = std::min(best_, *makespan);
    }

    const Instance& in_;
    std::vector<int> eastLeft_;
    std::vector<int> westLeft_;
    std::vector<int> pairCity_;
    std::vector<bool> opened_;
    std::vector<bool> closed_;
    std::vector<std::vector<Task>> sequences_;
    Int best_ = infinity;
};

/// Calls f(counts) for every multiset of size k over n elements, as per-element counts.
inline void forEachMultiset(int n, int k, const std::function<void(const std::vector<int>&)>& f)
{
    std::vector<int> counts(n, 0);
    std::function<void(int, int)> rec = [&](int element, int left)
    {
        if(element == n - 1)
        {
            counts[element] = left;
            f(counts);
            counts[element] = 0;
            return;
        }
        for(int c = left; c >= 0; --c)
        {
            counts[element] = c;
            rec(element + 1, left - c);
        }
        counts[element] = 0;
    };
    if(n > 0)
        rec(0, k);
}

/// Calls f(beta) for every sub-multiset beta of the per-element bounds.
inline void forEachSubMultiset(const std::vector<int>& bound,
    const std::function<void(const std::vector<int>&)>& f)
{
    std::vector<int> counts(bound.size(), 0);
    std::function<void(std::size_t)> rec = [&](std::size_t element)
    {
        if(element == bound.size())
        {
            f(counts);
            return;
        }
        for(int c = 0; c <= bound[element]; ++c)
        {
            counts[element] = c;
            rec(element + 1);
        }
        counts[element] = 0;
    };
    rec(0);
}

/// Exact optimal makespan of the PPP (e, w) given as per-city counts.
inline Int optimalMakespan(const Instance& in,
    const std::vector<int>& eastCount,
    const std::vector<int>& westCount)
{
    const auto n = eastCount.size();
    std::vector<int> common(n);
    for(std::size_t i = 0; i < n; ++i)
        common[i] = std::min(eastCount[i], westCount[i]);

    Int best = infinity;
    forEachSubMultiset(common, [&](const std::vector<int>& beta)
    {
        std::vector<int> alphaE(eastCount), alphaW(westCount), betaCities;
        for(std::size_t i = 0; i < n; ++i)
        {
            alphaE[i] -= beta[i];
            alphaW[i] -= beta[i];
            for(int k = 0; k < beta[i]; ++k)
                betaCities.push_back(static_cast<int>(i));
        }
        ScheduleSearch search(in, alphaE, alphaW, betaCities);
        best = std::min(best, search.run(best));
    });
    return best;
}

////////////////////////////////////////////////////////////
/// \brief Exact Pareto front (cost -> makespan), restricted
/// to the PPP space of the model above.
////////////////////////////////////////////////////////////
inline std::map<Int, Int> paretoFront(const Instance& in)
{
    const int n = static_cast<int>(in.cost.size());
    const int t = static_cast<int>(in.travelers);
    const int p = static_cast<int>(in.planes);
    if(n == 0 || p < 1 || t <= p)
        throw std::domain_error("oracle: need n >= 1 and t > p >= 1");

    std::map<Int, Int> bestPerCost;
    forEachMultiset(n, t, [&](const std::vector<int>& e)
    {
        forEachMultiset(n, t - p, [&](const std::vector<int>& w)
        {
            Int cost = 0;
            for(int i = 0; i < n; ++i)
                cost += (e[i] + w[i]) * in.cost[i];
            const Int makespan = optimalMakespan(in, e, w);
            auto it = bestPerCost.find(cost);
            if(it == bestPerCost.end() || makespan < it->second)
                bestPerCost[cost] = makespan;
        });
    });

    // Keep only non-dominated points: makespan strictly decreasing with cost.
    std::map<Int, Int> front;
    Int bestMakespan = infinity;
    for(const auto& [cost, makespan] : bestPerCost)
    {
        if(makespan < bestMakespan)
        {
            front[cost] = makespan;
            bestMakespan = makespan;
        }
    }
    return front;
}

} // namespace oracle

#endif // _ZS_ORACLE_BRUTE_FORCE_
