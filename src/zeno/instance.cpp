#include <zeno/instance.hpp>

#include <algorithm>
#include <stdexcept>
#include <string>

namespace zeno
{
void Instance::validate() const
{
    if(n() < 1)
        throw std::invalid_argument("an instance needs at least one central city");
    if(p < 1)
        throw std::invalid_argument("an instance needs at least one plane");
    if(t < p)
        throw std::invalid_argument("the number of planes (" + std::to_string(p) + ") exceeds the number of passengers (" + std::to_string(t) + ")");
    if(dbar.size() != d.size() || c.size() != d.size())
        throw std::invalid_argument("durations and costs must have one value per central city");
    const auto negative = [](const auto& v) { return std::ranges::any_of(v, [](auto x) { return x < 0; }); };
    if(negative(d) || negative(dbar) || negative(c))
        throw std::invalid_argument("durations and costs must be non-negative");
    if(central)
    {
        const auto size = d.size();
        if(central->size() != size || std::ranges::any_of(*central, [&](const auto& row) { return row.size() != size; }))
            throw std::invalid_argument("the central-flight table must have n rows of n values");
        for(std::size_t i = 0; i < size; ++i)
        {
            if((*central)[i][i] != 0)
                throw std::invalid_argument("the central-flight table must have a zero diagonal");
            for(std::size_t j = 0; j < size; ++j)
            {
                if((*central)[i][j] < 0)
                    throw std::invalid_argument("central-flight durations must be non-negative");
                if((*central)[i][j] != (*central)[j][i])
                    throw std::invalid_argument("the central-flight table must be symmetric: flights are undirected");
            }
        }
    }
}

Time Instance::centralFlight(int i, int j) const
{
    const auto a = static_cast<std::size_t>(i), b = static_cast<std::size_t>(j);
    if(central)
        return (*central)[a][b];
    return std::max(d[a], dbar[a]) + std::max(d[b], dbar[b]) + 100;
}

Front paretoFilter(std::vector<FrontPoint> points)
{
    // By makespan, then cost: a point is kept iff its cost is below every cost
    // seen at a smaller or equal makespan.
    std::ranges::sort(points, [](const FrontPoint& a, const FrontPoint& b) {
        return a.makespan != b.makespan ? a.makespan < b.makespan : a.cost < b.cost;
    });
    Front front;
    for(const auto& point : points)
        if(front.empty() || point.cost < front.back().cost)
        {
            if(!front.empty() && front.back().makespan == point.makespan)
                continue; // same makespan, higher cost (sorted)
            front.push_back(point);
        }
    return front;
}
} // namespace zeno
