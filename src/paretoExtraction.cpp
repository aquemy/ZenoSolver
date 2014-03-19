#include <map>
#include <paretoExtraction.hpp>

std::map<int, int> paretoExtraction(std::map<int, int>& front)
{

    std::map<int, int> pareto;
   
    auto current = begin(front);
    
    // Add the first
    pareto[current->first] = current->second;
    current++;
    
    for(auto it = begin(front); it != end(front); ++it)
    {
        if(it->second < current->second)
        {
            pareto[it->first] = it->second;
            current = it;
        }   
    }
    
    return pareto;
}
