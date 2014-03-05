#include <algorithm>
#include <vector>
#include <set>
#include <algorithm.hpp>
#include <ppp.hpp>
#include <powerSetGenerator.hpp>

#include <iostream> // Only debug

//bool compM(Si& i, Si& j) { return i.m < j.m; }
bool compM(const Si i, const Si j) { return i.m < j.m; }
bool compMS(Si& i, Si& j) 
{ 
    if(i.s == true and j.s == false)
        return true;
    else if(i.s == false and j.s == true)
        return false;
    else
        return i.m < j.m;
}

double SimpleUpperBound(const PPP& ppp, 
    const std::vector<std::vector<int>>& E,
    const std::vector<std::vector<int>>& W,
    const std::vector<double>& d, 
    unsigned p)
{     
    using std::begin;
    using std::end;

    std::vector<Si> S(p);
    
    auto rbegin = [](decltype(E[ppp.e]) v) { return v.rbegin(); };
    auto rend = [](decltype(E[ppp.e]) v) { return v.rend(); };
    
    auto itE = rbegin(E[ppp.e]);
    auto itW = rbegin(W[ppp.w]);
    auto itP = begin(S);
    
    while(itW < rend(W[ppp.w]))
    {
        itP = min_element(begin(S), end(S), compM);
        if(itP->s)
        {
            itP->m += 2*d[*itE];
            itP->s = false;
            itE++;
        }
        else
        {
            itP->m += 2*d[*itW];
            itP->s = true;
            itW++;
        }
    }
    
    while(itE < rend(E[ppp.e]))
    {
        itP = min_element(begin(S),end(S),compMS);
        itP->m += 2*d[*itE];
        itP->s = false;
        itE++;
    }
      
    return max_element(begin(S), end(S), compM)->m;
}

double UpperBound(const PPP& ppp, 
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W,
    const std::vector<double>& d, 
    unsigned p, 
    unsigned beta)
{
    using std::begin;
    using std::end;
    
    // Little trick waiting for C++14
    auto rbegin = [](decltype(E[ppp.e]) v) { return v.rbegin(); };
    auto rend = [](decltype(E[ppp.e]) v) { return v.rend(); };

    std::set<std::vector<unsigned>> betaPowerSet;
    generatePowerSet(ppp.betaMax, beta, ppp.betaSet, betaPowerSet);
    
    auto bestM = ppp.Mc;
    
    for(auto betaSet : betaPowerSet)
    {
        // Delete elements of the betaSet from w        
        std::vector<int> alphaWSet;
        std::set_difference (begin(W[ppp.w]), end(W[ppp.w]), begin(betaSet), end(betaSet), std::back_inserter(alphaWSet));
        
        // Delete elements of the betaSet from e        
        std::vector<int> alphaESet;
        std::set_difference(begin(E[ppp.e]), end(E[ppp.e]), begin(betaSet), end(betaSet), std::back_inserter(alphaESet));
    
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
                itP->s = false;
                itE++;
            }
            else
            {
                itP->m += 2*d[*itW];
                itP->s = true;
                itW++;
            }
        }
        
        while(itE < rend(alphaESet))
        {
            itP = min_element(begin(S),end(S),compMS);
            itP->m += 2*d[*itE];
            itP->s = false;
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

    }
            
    return bestM; 
}

bool isGreedilyDominated(const PPP& ppp, const std::vector<PPP>& PPPSet)
{
    for(const auto& j : PPPSet)
        if((j != ppp) && ((j.C <= ppp.C) && (j.Mc < ppp.Ms))) 
            return true;

    return false;
}

