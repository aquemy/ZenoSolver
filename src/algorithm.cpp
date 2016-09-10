#include <algorithm>
#include <vector>
#include <iterator>
#include <set>
#include <algorithm.hpp>
#include <powerSetGenerator.hpp>

#include <iostream>

//#define DEBUG

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
    const std::vector<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p,
    bool symetric)
{
    return symetric ? UpperBound_Symetric(Mc, Ml, e, w, betaPowerSet, d, de, p) : UpperBound_NonSymetric(Mc, Ml, e, w, betaPowerSet, d, de, p);
}


int UpperBound_Symetric(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p)
{
    using std::begin;
    using std::end;
    
    // Little trick waiting for C++14
    auto rbegin = [](decltype(e) v) { return v.rbegin(); };
    auto rend = [](decltype(e) v) { return v.rend(); };

    auto bestM = Mc;
    #ifdef DEBUG
    std::cerr << "PPP: (";
    for(auto i: e)
        std::cerr << i << ",";
    std::cerr << ")(";
    for(auto i: w)
        std::cerr << i << ",";
    std::cerr << ")" << std::endl;
    
    std::vector<unsigned> bestBetaSet;
    #endif
    for(auto betaSet : betaPowerSet)
    {
        #ifdef DEBUG
        std::cerr << "    betaS: {";
        for(auto i: betaSet)
            std::cerr << i << ",";
        std::cerr << "}" << std::endl;
        #endif
        
        // Delete elements of the betaSet from w        
        std::vector<int> alphaWSet(w.size() - betaSet.size());
        std::set_difference (begin(w), end(w), begin(betaSet), end(betaSet), begin(alphaWSet));

        // Delete elements of the betaSet from e        
        std::vector<int> alphaESet(e.size() - betaSet.size());
        std::set_difference(begin(e), end(e), begin(betaSet), end(betaSet), begin(alphaESet));
    
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
                itP->m += d[*itE] + de[*itE];
                itP->s = WEST;
                itE++;
            }
            else
            {
                itP->m += d[*itW] + de[*itW];
                itP->s = EAST;
                itW++;
            }
        }
        
        while(itE < rend(alphaESet))
        {
            itP = min_element(begin(S),end(S),compMS);
            itP->m += d[*itE] + de[*itE];
            itP->s = WEST;
            itE++;
        }

        // Pattern 3
        for(auto i : betaSet)
        {
            // Place only the element we need in order to avoid complete sorting
            std::nth_element(begin(S), begin(S)+1, end(S), compM);
            itP = min_element(begin(S), end(S), compM);
            auto maxSide = std::max(d[i], de[i]);
            auto minSide = std::min(d[i], de[i]);
            itP->m += 2*maxSide;
            (itP + 1)->m += 2*minSide;
        }
        auto b = std::max_element(begin(S),end(S), compM)->m;
        if(bestM > b) {
            bestM = b;
            #ifdef DEBUG
            bestBetaSet = betaSet;
            #endif
        }
        if(bestM == Ml) {
            #ifdef DEBUG
            bestBetaSet = betaSet;
            #endif
            break;
        }
    }
    #ifdef DEBUG
    std::cerr << "        BEST ML: " << bestM << " | BetaS: {";
    for(auto i: bestBetaSet)
        std::cerr << i << ",";
    std::cerr << "}" << std::endl;
    #endif
    return bestM; 
}

int UpperBound_NonSymetric(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p)
{
    using std::begin;
    using std::end;
    
    // Little trick waiting for C++14
    auto rbegin = [](decltype(e) v) { return v.rbegin(); };
    auto rend = [](decltype(e) v) { return v.rend(); };

    auto bestM = Mc;
    #ifdef DEBUG
    std::cerr << "PPP: (";
    for(auto i: e)
        std::cerr << i << ",";
    std::cerr << ")(";
    for(auto i: w)
        std::cerr << i << ",";
    std::cerr << ")" << std::endl;
    
    std::vector<unsigned> bestBetaSet;
    #endif
    unsigned i = 0;
    auto betaSize = betaPowerSet.size();
    for(auto betaSet : betaPowerSet)
    {
        i++;
        #ifdef DEBUG
        std::cerr << "    betaS: {";
        for(auto i: betaSet)
            std::cerr << i << ",";
        std::cerr << "}" << std::endl;
        #endif

        auto betaSetSize = betaSet.size();
        // Delete elements of the betaSet from w        
        std::vector<int> alphaWSet(w.size() - betaSetSize);
        std::set_difference (begin(w), end(w), begin(betaSet), end(betaSet), begin(alphaWSet));
        
        // Delete elements of the betaSet from e        
        std::vector<int> alphaESet(e.size() - betaSetSize);
        std::set_difference(begin(e), end(e), begin(betaSet), end(betaSet), begin(alphaESet));
    
        std::vector<Si> S(p);
        
        auto itE = rbegin(alphaESet);
        auto itW = rbegin(alphaWSet);
        auto itP = begin(S);

        // Open the P3
        if(p >= betaSetSize) { // Avoid finding the min element that is costly
           for(unsigned i = 0; i < betaSetSize; ++i)
                S[i].m = 2*std::max(d[betaSet[i]], de[betaSet[i]]);
        }
        else {
            for(auto i : betaSet)
            {
                itP = min_element(begin(S), end(S), compM);
                itP->m += 2*std::max(d[i], de[i]);
            }
        }

        // We give one P1 to every plane by plan constraint
        for(unsigned i = 0; i < p; ++i) 
        {
            itP = min_element(begin(S), end(S), compM);
            itP->m += d[*itE] + de[*itE];
            itE++;
        }

        while(itW < rend(alphaWSet))
        {
            itP = min_element(begin(S), end(S), compM);
            itP->m += d[*itE] + de[*itE];
            itE++;
            itP->m += d[*itW] + de[*itW];
            itW++;
        }

        // We close the P3
        for(auto i : betaSet)
        {
            itP = min_element(begin(S), end(S), compM);
            itP->m += 2*std::min(d[i], de[i]);
        }

        auto b = std::max_element(begin(S),end(S), compM)->m;
        if(bestM > b) {
            bestM = b;
            #ifdef DEBUG
            bestBetaSet = betaSet;
            #endif
        }
        if(bestM == Ml) {
            #ifdef DEBUG
            bestBetaSet = betaSet;
            std::cerr << "[!]     BEST: " << Ml << " (" << i << "/" << betaSize << ")" << std::endl;
            #endif
            break;
        }
    }
    #ifdef DEBUG
    std::cerr << "        BEST ML: " << bestM << " | BetaS: {";
    for(auto i: bestBetaSet)
        std::cerr << i << ",";
    std::cerr << "}" << std::endl;
    #endif
    return bestM; 
}