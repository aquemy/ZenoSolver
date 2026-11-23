#include <iterator>
#include <map>
#include <paretoExtraction.hpp>

namespace
{

// The front is sorted by increasing cost, so a point is Pareto-optimal iff
// its makespan is strictly lower than the makespan of the last point kept.
template<class Value, class Makespan>
std::map<int, Value> extract(const std::map<int, Value>& front, Makespan makespan)
{
    std::map<int, Value> pareto;
    if(front.empty())
        return pareto;

    auto current = front.begin();
    pareto.insert(*current);

    for(auto it = std::next(front.begin()); it != front.end(); ++it)
    {
        if(makespan(it->second) < makespan(current->second))
        {
            pareto.insert(pareto.end(), *it);
            current = it;
        }
    }

    return pareto;
}

} // namespace

std::map<int, int> paretoExtraction(std::map<int, int>& front)
{
    return extract(front, [](int m) { return m; });
}

std::map<int, Plan> paretoExtractionPlan(std::map<int, Plan>& front)
{
    return extract(front, [](const Plan& plan) { return plan.m; });
}
