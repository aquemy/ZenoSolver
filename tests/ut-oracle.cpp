////////////////////////////////////////////////////////////
/// \file ut-oracle.cpp
/// \brief Hand-checked cases for the brute-force oracle, so the
/// oracle itself is trusted before it judges the solvers.
////////////////////////////////////////////////////////////

#include <iostream>
#include <map>
#include <string>

#include "oracle/bruteForce.hpp"

namespace {

int failures = 0;

void check(bool ok, const std::string& what)
{
    if(!ok)
    {
        std::cerr << "FAILED: " << what << std::endl;
        ++failures;
    }
}

oracle::Instance symmetric(std::vector<oracle::Int> cost, std::vector<oracle::Int> d, unsigned t, unsigned p)
{
    oracle::Instance in;
    in.cost = std::move(cost);
    in.west = d;
    in.east = d;
    in.travelers = t;
    in.planes = p;
    return in;
}

} // namespace

int main()
{
    using oracle::Int;
    using oracle::Kind;
    using oracle::Task;

    // One plane, two travelers, two cities: d = (1, 2), c = (2, 1).
    // With a single plane every schedule is sequential, so the makespan of
    // a PPP is 2 * sum(d) over its 3 landings. k landings in city 0 give
    // cost 3 + k and makespan 12 - 2k, so all 4 points are Pareto-optimal.
    {
        auto in = symmetric({2, 1}, {1, 2}, 2, 1);
        std::map<Int, Int> expected{{3, 12}, {4, 10}, {5, 8}, {6, 6}};
        check(oracle::paretoFront(in) == expected, "n=2 t=2 p=1 front");
    }

    // Two planes, three travelers, a single city of duration 1: every PPP is
    // e = (0,0,0), w = (0). Without P3: plane A does E W E (6), plane B does E
    // (2): makespan 6. With one P3: A does Open E (4), B does E Close (4),
    // B arrives at c_0 at time 3 and the drop happened at time 1: makespan 4.
    {
        auto in = symmetric({5}, {1}, 3, 2);
        std::vector<int> e{3}, w{1};
        check(oracle::optimalMakespan(in, e, w) == 4, "single city P3 makespan");
    }

    // The simulator makes a Close wait for its Open.
    {
        auto in = symmetric({1, 1}, {1, 10}, 2, 2);
        // Plane 0: Open(city 1) then East(city 0): drops at 10, ends at 22.
        // Plane 1: East(city 0) then Close(city 1): arrives at c_1 at 12,
        // the traveler is there since 10, picks up, ends at 22.
        std::vector<std::vector<Task>> seq{
            {Task{Kind::Open, 1, 0}, Task{Kind::East, 0, -1}},
            {Task{Kind::East, 0, -1}, Task{Kind::Close, 1, 0}}};
        auto m = oracle::simulate(in, seq, 1);
        check(m && *m == 22, "no wait needed");

        // An Open after an East would start from the east side: invalid.
        std::vector<std::vector<Task>> bad{
            {Task{Kind::East, 0, -1}, Task{Kind::Open, 1, 0}},
            {Task{Kind::East, 0, -1}, Task{Kind::Close, 1, 0}}};
        check(!oracle::simulate(in, bad, 1), "Open on the east side is rejected");

        // Close before Open on the same plane deadlocks.
        std::vector<std::vector<Task>> deadlock{
            {Task{Kind::East, 0, -1}, Task{Kind::Close, 1, 0}, Task{Kind::West, 0, -1},
             Task{Kind::Open, 1, 0}, Task{Kind::East, 0, -1}}};
        check(!oracle::simulate(in, deadlock, 1), "deadlock is rejected");
    }

    // Waiting: plane 1 reaches c_1 before the drop and waits.
    {
        oracle::Instance in;
        in.cost = {1, 1};
        in.west = {1, 10};
        in.east = {1, 1};
        in.travelers = 2;
        in.planes = 2;
        // Plane 0: Open(1): drop at 10, back at 20. Then East(0): 22.
        // Plane 1: East(0): at G at 2. Close(1): arrives at c_1 at 3, waits
        // until 10, back at G at 11.
        std::vector<std::vector<Task>> seq{
            {Task{Kind::Open, 1, 0}, Task{Kind::East, 0, -1}},
            {Task{Kind::East, 0, -1}, Task{Kind::Close, 1, 0}}};
        auto m = oracle::simulate(in, seq, 1);
        check(m && *m == 22, "waiting close");
        std::vector<std::vector<Task>> seq2{
            {Task{Kind::Open, 1, 0}},
            {Task{Kind::East, 0, -1}, Task{Kind::Close, 1, 0}}};
        // Plane 0 never crosses east: rejected by the search, but the
        // simulator itself only checks sides and deadlocks.
        auto m2 = oracle::simulate(in, seq2, 1);
        check(m2 && *m2 == 20, "waiting close, makespan set by plane 0");
    }

    // Multiset enumeration sizes: C(n+k-1, k).
    {
        int count = 0;
        oracle::forEachMultiset(3, 4, [&](const std::vector<int>&) { ++count; });
        check(count == 15, "multisets of size 4 over 3 elements");
        count = 0;
        oracle::forEachSubMultiset({2, 0, 1}, [&](const std::vector<int>&) { ++count; });
        check(count == 6, "sub-multisets of {0,0,2}");
    }

    if(failures == 0)
        std::cout << "all oracle checks passed" << std::endl;
    return failures == 0 ? 0 : 1;
}
