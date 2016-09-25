#include <vector>
#include <set>
#include <algorithm>
#include <powerSetGenerator.hpp>

#include <iostream>

void naive::addSubSet(uint64_t x, const std::vector<int>& values, std::set<std::vector<int>>& s, unsigned n)
{
    std::vector<int> subset;
    for(auto i = 1; x; x >>= 1, ++i)
        if (x & 1) subset.push_back(values[i-1]);
    s.insert(subset);
}

uint64_t naive::nextSubSet (uint64_t sub, uint64_t set) {
   uint64_t tmp = sub-1;
   uint64_t rip = set & (tmp + (sub & (0-sub)) - set);
   for(sub = (tmp & sub) ^ rip; sub &= sub-1; rip ^= tmp, set ^= tmp)
       tmp = set & (0-set);
   return rip;
}

void naive::generatePowerSet(unsigned i, const std::vector<int>& values, std::set<std::vector<int>>& s)
{
    const unsigned n = values.size();
    auto set = (1ULL << n) - 1;
    auto sub = (1ULL << i) - 1;
    uint64_t x = sub; 
    uint64_t y;
    do {            
        addSubSet(x, values, s, i);
        y = nextSubSet(x, set);
        x = y;
    } while ((y > sub));
}
