////////////////////////////////////////////////////////////
/// \file ut-paretoExtraction.cpp
/// \brief The front maps a cost to its best makespan. A point
/// is Pareto-optimal iff its makespan is strictly lower than
/// the makespan of every cheaper point.
////////////////////////////////////////////////////////////

#include <iostream>
#include <map>
#include <string>

#include <paretoExtraction.hpp>

namespace {

int failures = 0;

void check(const std::string& what, std::map<int, int> front, const std::map<int, int>& expected)
{
    const auto actual = paretoExtraction(front);
    if(actual != expected)
    {
        std::cerr << "FAILED: " << what << " ->";
        for(const auto& point : actual)
            std::cerr << " (" << point.first << "," << point.second << ")";
        std::cerr << std::endl;
        ++failures;
    }

    // Same front, carried by plans.
    std::map<int, Plan> plans;
    for(const auto& point : front)
    {
        Plan plan(1);
        plan.c = point.first;
        plan.m = point.second;
        plans[point.first] = plan;
    }
    std::map<int, int> fromPlans;
    for(const auto& point : paretoExtractionPlan(plans))
        fromPlans[point.first] = point.second.m;
    if(fromPlans != expected)
    {
        std::cerr << "FAILED (plans): " << what << std::endl;
        ++failures;
    }
}

} // namespace

int main()
{
    check("all points are optimal",
        {{1, 10}, {2, 5}, {3, 4}},
        {{1, 10}, {2, 5}, {3, 4}});

    check("the second point is optimal, the third is dominated",
        {{1, 10}, {2, 5}, {3, 7}},
        {{1, 10}, {2, 5}});

    check("the second point is dominated",
        {{1, 10}, {2, 12}, {3, 4}},
        {{1, 10}, {3, 4}});

    check("an equal makespan at a higher cost is dominated",
        {{1, 10}, {2, 10}, {3, 9}, {4, 9}},
        {{1, 10}, {3, 9}});

    check("a single point", {{7, 3}}, {{7, 3}});

    check("two points", {{1, 4}, {2, 3}}, {{1, 4}, {2, 3}});

    check("an empty front", {}, {});

    if(failures == 0)
        std::cout << "all Pareto extraction checks passed" << std::endl;
    return failures == 0 ? 0 : 1;
}
