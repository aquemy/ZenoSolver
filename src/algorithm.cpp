#include <algorithm>
#include <vector>
#include <set>
#include <algorithm.hpp>
#include <powerSetGenerator.hpp>

bool compM(const Si i, const Si j) 
{ 
    return i.m < j.m; 
}

bool compMS(Si& i, Si& j) 
{ 
    if(i.s == EAST and j.s == WEST)
        return true;
    else if(i.s == WEST and j.s == EAST)
        return false;
    else
        compM(i,j);
}

int UpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::set<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    unsigned p)
{
    using std::begin;
    using std::end;
    
    // Little trick waiting for C++14
    auto rbegin = [](decltype(e) v) { return v.rbegin(); };
    auto rend = [](decltype(e) v) { return v.rend(); };

    auto bestM = Mc;
    
    for(auto betaSet : betaPowerSet)
    {
        // Delete elements of the betaSet from w        
        std::vector<int> alphaWSet;
        std::set_difference (begin(w), end(w), begin(betaSet), end(betaSet), std::back_inserter(alphaWSet));
        
        // Delete elements of the betaSet from e        
        std::vector<int> alphaESet;
        std::set_difference(begin(e), end(e), begin(betaSet), end(betaSet), std::back_inserter(alphaESet));
    
        std::vector<Si> S(p);
        
        auto itE = rbegin(alphaESet);
        auto itW = rbegin(alphaWSet);
        auto itP = begin(S);
    
        // Perform the greedy algorithm
        while(itW < rend(alphaWSet))
        {
            itP = min_element(begin(S), end(S), compM);
            if(itP->s)
            {
                itP->m += 2*d[*itE];
                itP->s = WEST;
                itE++;
            }
            else
            {
                itP->m += 2*d[*itW];
                itP->s = EAST;
                itW++;
            }
        }
        
        while(itE < rend(alphaESet))
        {
            itP = min_element(begin(S),end(S),compMS);
            itP->m += 2*d[*itE];
            itP->s = WEST;
            itE++;
        }
        
        // Pattern 3
        for(auto i : betaSet)
        {
            // Place only the element we need in order to avoid complete sorting
            std::nth_element(begin(S), begin(S)+1, end(S), compM);
            itP = min_element(begin(S), end(S), compM);
            itP->m += 2*d[i];
            (itP + 1)->m += 2*d[i];
        }
        
        if(bestM > std::max_element(begin(S),end(S), compM)->m)
            bestM = std::max_element(begin(S),end(S), compM)->m;
        if(bestM == Ml)
            return Ml;
    }
            
    return bestM; 
}

