#include <zeno/solve.hpp>

#include <zeno/breakpoints.hpp>
#include <zeno/one_plane.hpp>
#include <zeno/parallel.hpp>
#include <zeno/reduce.hpp>

#include <algorithm>
#include <chrono>
#include <mutex>
#include <stdexcept>
#include <string>
#include <vector>

namespace zeno
{
namespace
{
using Clock = std::chrono::steady_clock;

double secondsSince(Clock::time_point start)
{
    return std::chrono::duration<double>(Clock::now() - start).count();
}

/// E(T) on the levels T = lowest + i, with the bracket L <= E <= U.
struct Levels
{
    Time lowest = 0;
    std::vector<Cost> lower, upper, value;
    std::vector<LevelSource> source;

    explicit Levels(Time lo, Time hi)
        : lowest(lo)
        , lower(static_cast<std::size_t>(hi - lo + 1), 0)
        , upper(static_cast<std::size_t>(hi - lo + 1), kInfCost)
        , value(static_cast<std::size_t>(hi - lo + 1), kInfCost)
        , source(static_cast<std::size_t>(hi - lo + 1), LevelSource::Unknown) {}

    [[nodiscard]] std::size_t size() const noexcept { return value.size(); }
    [[nodiscard]] bool known(std::size_t i) const noexcept { return source[i] != LevelSource::Unknown; }
    [[nodiscard]] Time level(std::size_t i) const noexcept { return lowest + static_cast<Time>(i); }

    void settle(std::size_t i, Cost v, LevelSource how)
    {
        if(v < lower[i] || v > upper[i])
            throw std::logic_error("solveFront: E(" + std::to_string(level(i)) + ") = " + std::to_string(v) +
                                   " lies outside its bracket [" + std::to_string(lower[i]) + ", " + std::to_string(upper[i]) + "]");
        value[i] = v;
        source[i] = how;
    }
};

class FrontSolver
{
public:
    /// Above this many levels, search for the breakpoints instead of sweeping.
    static constexpr Time kSweepLevels = Time{1} << 12;

    FrontSolver(const ReducedInstance& r, const SolveOptions& options, SolveStats& stats)
        : r_(r)
        , threads_(workerCount(options.threads))
        , stats_(stats)
        , sweep_(options.levels == LevelStrategy::Sweep ||
                 (options.levels == LevelStrategy::Automatic && r.highestLevel() - r.lowestLevel() + 1 <= kSweepLevels))
        , levels_(r.lowestLevel(), sweep_ ? r.highestLevel() : r.lowestLevel())
        , G_(build(r, options.table, stats))
    {}

    /// Plans for the front points, from the smallest tree bound that reaches E.
    std::vector<Plan> plans(const Instance& instance, const Front& front)
    {
        const auto start = Clock::now();
        std::vector<Plan> out(front.size());
        parallelFor(front.size(), threads_, [&](std::size_t i) {
            const Time T = front[i].makespan / r_.makespanPerLevel;
            std::vector<int> bounds;
            for(int q : {2, 3})
                if(q < r_.maxTree())
                    bounds.push_back(q);
            bounds.push_back(r_.maxTree());
            for(int q : bounds)
            {
                const ForestProgram program(r_, G_, T, q);
                if(program.value() != front[i].cost)
                    continue;
                out[i] = buildPlan(instance, r_, program.reconstruct());
                const PlanCheck check = checkPlan(instance, out[i]);
                if(!check.ok || check.cost != front[i].cost || check.makespan != front[i].makespan)
                    throw std::logic_error("solveFront: the plan of the point (" + std::to_string(front[i].cost) + ", " +
                                           std::to_string(front[i].makespan) + ") fails its check: " +
                                           (check.ok ? "cost " + std::to_string(check.cost) + ", makespan " + std::to_string(check.makespan) : check.error));
                return;
            }
            throw std::logic_error("solveFront: no forest realises a front point");
        });
        stats_.secondsPlans = secondsSince(start);
        return out;
    }

    Front run()
    {
        stats_.levels = static_cast<std::uint64_t>(r_.highestLevel() - r_.lowestLevel() + 1);
        return sweep_ ? runSweep() : runSearch();
    }

private:
    // Every level: the bracket on all of them, then the exact DP where needed.
    Front runSweep()
    {
        bracket();
        if(r_.maxTree() >= 3)
            chains();

        // The cheapest point is known in closed form; the fastest is computed.
        const std::size_t last = levels_.size() - 1;
        if(!levels_.known(last))
            levels_.settle(last, static_cast<Cost>(r_.landings()) * r_.c[static_cast<std::size_t>(r_.cheapest())], LevelSource::Closed);
        if(!levels_.known(0))
            evaluate({0});
        bisect(0, last);
        return extract();
    }

    // E at one level, from the cheapest bound that settles it.
    Cost valueAt(Time T, LevelSource& how)
    {
        LevelStats work;
        const Cost L = relaxedCost(r_, G_, T, &work);
        Cost U = forestCost(r_, G_, T, 2, &work);
        Cost value = U;
        how = L == U ? LevelSource::Bracket : LevelSource::Pairs;
        if(L != U && r_.maxTree() >= 3)
        {
            U = std::min(U, forestCost(r_, G_, T, 3, &work));
            value = U;
            how = LevelSource::Chains;
            if(L != U && r_.maxTree() > 3)
            {
                value = forestCost(r_, G_, T, r_.maxTree(), &work);
                how = LevelSource::Exact;
            }
        }
        if(value < L || value > U)
            throw std::logic_error("solveFront: E(" + std::to_string(T) + ") outside its bracket");
        addWork(work);
        return value;
    }

    // Few breakpoints over many levels: bisect for them (zeno::breakpoints).
    Front runSearch()
    {
        const Time lo = r_.lowestLevel(), hi = r_.highestLevel();
        const auto value = [&](Time T) {
            LevelSource how{};
            const Cost v = valueAt(T, how);
            const std::scoped_lock lock(statsMutex_);
            count(how);
            return v;
        };
        const Cost Elo = value(lo);
        const Cost Ehi = static_cast<Cost>(r_.landings()) * r_.c[static_cast<std::size_t>(r_.cheapest())];
        const auto start = Clock::now();
        const auto points = breakpoints(lo, Elo, hi, Ehi, value, threads_);
        stats_.secondsExact += secondsSince(start);
        Front front;
        for(const auto& [T, E] : points)
            front.push_back({E, r_.makespanPerLevel * T});
        return front;
    }

    void count(LevelSource how)
    {
        switch(how)
        {
            case LevelSource::Bracket: ++stats_.closedByBracket; break;
            case LevelSource::Pairs: ++stats_.closedByPairs; break;
            case LevelSource::Chains: ++stats_.closedByChains; break;
            case LevelSource::Exact: ++stats_.exactCalls; break;
            default: break;
        }
    }

    static OnePlaneTable build(const ReducedInstance& r, OnePlaneTable::Layout layout, SolveStats& stats)
    {
        const auto start = Clock::now();
        OnePlaneTable G(r.fill, r.c, r.maxGroup(), r.highestLevel(), layout);
        stats.secondsTable = secondsSince(start);
        return G;
    }

    void addWork(const LevelStats& work)
    {
        const std::scoped_lock lock(statsMutex_);
        stats_.work.states += work.states;
        stats_.work.relaxations += work.relaxations;
    }

    // L and U on every level. U is exact when trees need at most 2 planes.
    void bracket()
    {
        const auto start = Clock::now();
        const bool pairsExact = r_.maxTree() <= 2;
        parallelFor(levels_.size(), threads_, [&](std::size_t i) {
            LevelStats work;
            const Time T = levels_.level(i);
            levels_.lower[i] = relaxedCost(r_, G_, T, &work);
            levels_.upper[i] = forestCost(r_, G_, T, 2, &work);
            if(levels_.lower[i] > levels_.upper[i])
                throw std::logic_error("solveFront: L > U at level " + std::to_string(T));
            if(levels_.lower[i] == levels_.upper[i])
                levels_.settle(i, levels_.upper[i], LevelSource::Bracket);
            else if(pairsExact)
                levels_.settle(i, levels_.upper[i], LevelSource::Pairs);
            addWork(work);
        });
        for(std::size_t i = 0; i < levels_.size(); ++i)
        {
            stats_.closedByBracket += levels_.source[i] == LevelSource::Bracket;
            stats_.closedByPairs += levels_.source[i] == LevelSource::Pairs;
        }
        stats_.secondsBracket = secondsSince(start);
    }

    // U3 on the open levels; exact when trees need at most 3 planes.
    void chains()
    {
        const auto start = Clock::now();
        std::vector<std::size_t> open;
        for(std::size_t i = 0; i < levels_.size(); ++i)
            if(!levels_.known(i))
                open.push_back(i);
        const bool chainsExact = r_.maxTree() <= 3;
        parallelFor(open.size(), threads_, [&](std::size_t k) {
            const std::size_t i = open[k];
            LevelStats work;
            const Cost u3 = forestCost(r_, G_, levels_.level(i), 3, &work);
            levels_.upper[i] = std::min(levels_.upper[i], u3);
            if(levels_.lower[i] == levels_.upper[i] || chainsExact)
                levels_.settle(i, levels_.upper[i], LevelSource::Chains);
            addWork(work);
        });
        for(std::size_t i : open)
            stats_.closedByChains += levels_.source[i] == LevelSource::Chains;
        stats_.secondsChains = secondsSince(start);
    }

    // Exact link-forest DP on the given levels, in parallel.
    void evaluate(const std::vector<std::size_t>& indices)
    {
        const auto start = Clock::now();
        parallelFor(indices.size(), threads_, [&](std::size_t k) {
            const std::size_t i = indices[k];
            LevelStats work;
            const Cost e = forestCost(r_, G_, levels_.level(i), r_.maxTree(), &work);
            levels_.settle(i, e, LevelSource::Exact);
            addWork(work);
        });
        stats_.exactCalls += indices.size();
        stats_.secondsExact += secondsSince(start);
    }

    // E is non-increasing. Between two known levels a < b, a level k has
    // E(b) <= E(k) <= E(a); with L <= E <= U the level is settled when the
    // tightened bounds meet. Otherwise evaluate up to `threads` evenly spaced
    // open levels and recurse on the pieces.
    void bisect(std::size_t a, std::size_t b)
    {
        if(b <= a + 1)
            return;
        const Cost high = levels_.value[a], low = levels_.value[b];
        std::vector<std::size_t> open;
        for(std::size_t k = a + 1; k < b; ++k)
        {
            if(levels_.known(k))
                continue;
            const Cost lo = std::max(levels_.lower[k], low), up = std::min(levels_.upper[k], high);
            levels_.lower[k] = lo;
            levels_.upper[k] = up;
            if(lo == up)
            {
                levels_.settle(k, lo, LevelSource::Monotone);
                ++stats_.closedByMonotonicity;
            }
            else
                open.push_back(k);
        }
        if(open.empty())
            return;
        const std::size_t picks = std::min<std::size_t>(open.size(), std::max(1u, threads_));
        std::vector<std::size_t> chosen;
        for(std::size_t j = 0; j < picks; ++j)
            chosen.push_back(open[(2 * j + 1) * open.size() / (2 * picks)]);
        evaluate(chosen);
        std::size_t from = a;
        for(std::size_t k : chosen)
        {
            bisect(from, k);
            from = k;
        }
        bisect(from, b);
    }

    Front extract() const
    {
        Front front;
        for(std::size_t i = 0; i < levels_.size(); ++i)
        {
            if(!levels_.known(i))
                throw std::logic_error("solveFront: a level was left unsettled");
            if(i > 0 && levels_.value[i] > levels_.value[i - 1])
                throw std::logic_error("solveFront: E increases at level " + std::to_string(levels_.level(i)));
            if(i == 0 || levels_.value[i] < levels_.value[i - 1])
                front.push_back({levels_.value[i], r_.makespanPerLevel * levels_.level(i)});
        }
        return front;
    }

    const ReducedInstance& r_;
    unsigned threads_;
    SolveStats& stats_;
    std::mutex statsMutex_;
    bool sweep_;
    Levels levels_;
    OnePlaneTable G_;
};
} // namespace

SolveResult solveFront(const Instance& instance, const SolveOptions& options)
{
    if(!instance.symmetric())
        throw std::invalid_argument("solveFront: non-symmetric instances are not supported yet");
    const ReducedInstance r = reduce(instance);
    SolveResult result;
    result.stats.lowestLevel = r.lowestLevel();
    result.stats.highestLevel = r.highestLevel();
    result.stats.scale = r.scale;
    result.stats.reducedCities = r.n();
    result.stats.maxTree = r.maxTree();
    FrontSolver solver(r, options, result.stats);
    result.front = solver.run();
    if(options.plans)
        result.plans = solver.plans(instance, result.front);
    return result;
}
} // namespace zeno
