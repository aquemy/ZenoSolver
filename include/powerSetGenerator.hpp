#ifndef _ZS_POWER_SET_GENERATOR_
#define _ZS_POWER_SET_GENERATOR_

#include <cstdint>

void addSubSet(uint64_t x, const std::vector<int>& values, std::vector<std::vector<unsigned>>& s);

uint64_t nextSubSet (uint64_t sub, uint64_t set);

void generatePowerSet(unsigned n, unsigned i, const std::vector<int>& values, std::vector<std::vector<unsigned>>& s);

#endif // _ZS_POWER_SET_GENERATOR_
