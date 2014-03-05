#ifndef _ZS_POWER_SET_GENERATOR_
#define _ZS_POWER_SET_GENERATOR_

#include <cstdint>
#include <set>

void addSubSet(uint64_t x, const std::vector<int>& values, std::set<std::vector<unsigned>>& s);

uint64_t nextSubSet (uint64_t sub, uint64_t set);

void generatePowerSet(unsigned n, unsigned i, const std::vector<int>& values, std::set<std::vector<unsigned>>& s);

#endif // _ZS_POWER_SET_GENERATOR_
