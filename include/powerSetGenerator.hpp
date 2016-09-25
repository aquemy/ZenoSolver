#ifndef _ZS_POWER_SET_GENERATOR_
#define _ZS_POWER_SET_GENERATOR_

#include <cstdint>
#include <vector>
#include <set>
#include <map>

namespace naive {

void addSubSet(uint64_t x, const std::vector<int>& values, std::set<std::vector<int>>& s, unsigned i);

uint64_t nextSubSet (uint64_t sub, uint64_t set);

////////////////////////////////////////////////////////////
/// \brief Generate the powerset according to a set of values.
///
/// \param i Number of elements in the powerset.
/// \param values Vector of values.
/// \param s Set to be filled with generated sets.
////////////////////////////////////////////////////////////

void generatePowerSet(unsigned i, const std::vector<int>& values, std::set<std::vector<int>>& s);

}; // end namespace naive

////////////////////////////////////////////////////////////
/// \brief Generate the powerset according to a set of values
/// and by using a precalculated map of value to occurrences.
///
/// The algorithm is iterative and require the set of (k-1)-
/// combinaison to generate the k-combinaisons.
///
/// \param prev Set of (k-1)-combinaisons.
/// \param values Vector of values.
/// \param mapping_v Contains the different possible value sorted.
/// \param mapping Map the value to the number of occurrences.
/// \param k Size of the combinaisons to generate.
/// \param n Highest possible value in a combinaison.
////////////////////////////////////////////////////////////
template<class T = std::less<int>>
std::vector<std::vector<int>> generatePowerSet(std::vector<std::vector<int>>& prev, 
  const std::vector<int>& values, 
  std::vector<int>& mapping_v, 
  std::map<int, std::pair<int, int>, T> mapping, 
  unsigned int k,
  unsigned int n) 
{
    if(k == 0)
    	return std::vector<std::vector<int>>{};
    if(k == values.size())
      	return std::vector<std::vector<int>>{values};
    // Handle initialization
    if(k == 1) 
    {
      	std::vector<std::vector<int>> res(n);
      	auto it = std::begin(res);
      	for(const auto i: mapping_v)
      	{
        	*it = std::vector<int>{i};
        	it++;
      	}
      	return res;
    }

    std::vector<std::vector<int>> res;
    for(auto c: prev) 
    {
      	auto mapping_start = c[k-2];
      	auto last_elem_count = 1;
      	if(k > 2) 
      	{
      		for(int i = k-2; i > 0; --i) {
        		if(c[i] != c[i-1])
          			break;
        		last_elem_count++;
      		}
    	}

	    if(last_elem_count >= mapping[mapping_start].first && mapping[mapping_start].second == n-1)
	    	continue;
	    auto d = std::vector<int>(c);
	    d.resize(d.size()+1);

	    if(last_elem_count >= mapping[mapping_start].first) {
	      	mapping_start = mapping_v[mapping[mapping_start].second + 1];
	    }

	    
	    for(auto i = std::begin(mapping_v) + mapping[mapping_start].second; i != std::end(mapping_v); ++i) 
	    {
			d[k-1] = *i;
	        res.push_back(d);
	    }
    }
    return res;
}

template<class T = std::less<int>>
int calculateMapping(const std::vector<int>& betaSetValue, std::map<int, std::pair<int, int>, T>& mapping, std::vector<int>& mapping_v) 
{
	unsigned i = 0;
	for(auto it: betaSetValue)
	{
     	if(mapping.count(it))
           	mapping[it].first++;
      	else {
          	mapping[it] = {1, i};
          	mapping_v.push_back(it);
          	++i;
     	}
 	}
 	return i;
}

#endif // _ZS_POWER_SET_GENERATOR_
