// Front of role-configuration schedules: the Pareto set of (cost, exact makespan) over balanced role
// configurations with exactly s = 2t - p landings, each scheduled with its best orders and matching
// (doc/theory/exact-front.md, §5). Uses the brute-force oracle of the tests (tests/oracle/bruteForce.hpp),
// whose tasks East/West/Open/Close are crossings, drop-offs and pick-ups, simulated with exact waiting.
//
// Comparing this front with the exhaustive search over all plans (truth.cpp) tests schedulable domination.
//
// Usage: config_front <d1,d2,...> <dbar1,dbar2,...> <c1,c2,...> <t> <p>
// Prints "cost makespan" lines.
#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

#include "../../../tests/oracle/bruteForce.hpp"

static std::vector<oracle::Int> parse(const std::string& s)
{
    std::vector<oracle::Int> v;
    std::size_t pos = 0;
    while(pos < s.size())
    {
        std::size_t q = s.find(',', pos);
        if(q == std::string::npos) q = s.size();
        v.push_back(std::atoll(s.substr(pos, q - pos).c_str()));
        pos = q + 1;
    }
    return v;
}

int main(int argc, char** argv)
{
    if(argc < 6) { std::fprintf(stderr, "usage: config_front d dbar c t p\n"); return 2; }
    oracle::Instance in;
    in.west = parse(argv[1]);
    in.east = parse(argv[2]);
    in.cost = parse(argv[3]);
    in.travelers = static_cast<unsigned>(std::atoi(argv[4]));
    in.planes = static_cast<unsigned>(std::atoi(argv[5]));
    for(const auto& [cost, makespan] : oracle::paretoFront(in))
        std::printf("%lld %lld\n", static_cast<long long>(cost), static_cast<long long>(makespan));
    return 0;
}
