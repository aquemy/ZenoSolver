#include <vector>
#include <set>
#include <algorithm>
#include <powerSetGenerator.hpp>

#include <iostream>

void addSubSet(uint64_t x, const std::vector<int>& values, std::set<std::vector<unsigned>>& s, unsigned n)
{
    std::vector<unsigned> subset;//(n);
    std::cout << "X " << (x >>= 1) << std::endl;
    for(auto i = 1; x; x >>= 1, ++i)
        if (x & 1) subset.push_back(values[i-1]);
    s.insert(subset);
}

uint64_t nextSubSet (uint64_t sub, uint64_t set) {
   uint64_t tmp = sub-1;
   uint64_t rip = set & (tmp + (sub & (0-sub)) - set);
   for(sub = (tmp & sub) ^ rip; sub &= sub-1; rip ^= tmp, set ^= tmp)
       tmp = set & (0-set);
   return rip;
}

void generatePowerSet(unsigned i, const std::vector<int>& values, std::set<std::vector<unsigned>>& s)
{
    std::cout << "GENERATE FOR " << i << std::endl;
    for(auto e: values)
      std::cout << e << " ";
    std::cout << std::endl;
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
    for(auto i: s) {
      for(auto e: i)
        std::cout << e << " ";
      std::cout << std::endl;
    }
    std::cout << "----------------" << std::endl;
}

std::vector<std::vector<unsigned>> new_powerSet(std::vector<int> sub) {
    std::vector<std::vector<unsigned>> s;
    for(unsigned i = sub.size(); i > 0; --i) {
          int k = i;
          if(sub.size() > 0) {
              auto ref = std::begin(sub);
              for(auto it = std::begin(sub); it != std::end(sub); ++it) {
                  if(*ref != *it) {
                      ref = it;
                  }
                  if(std::distance(ref, it) >= k) {
                      sub.erase(it);
                      it--;
                  }  
              }
          }
          std::vector<unsigned> combi(k);
          for(auto it = std::begin(sub); it+(k-1) != std::end(sub); ++it) {

              for(unsigned i = 0; i < k; ++i) {
                  combi[i] = *(it+i);
              }
              s.push_back(combi);
          }
      }
      return s;
}