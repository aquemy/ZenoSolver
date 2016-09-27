#include <algorithm>
#include <vector>
#include <iterator>
#include <set>
#include <algorithm.hpp>
#include <powerSetGenerator.hpp>

#include <iostream>

//#define DEBUG

std::ostream& operator <<(std::ostream& stream, const Plan& plan) {
    auto i = int{0};
    for(auto plane: plan.cities) {
        stream << "P_" << i << ": C_I";
        for(auto city: plane) {
            stream << " -> C_" << city;
        }
        stream << " -> C_G (M: " << plan.planes_m[i] << ")" << std::endl;
        ++i;
    }
    return stream;
}

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

int ComputeUpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<std::vector<int>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p,
    bool symetric,
    int& countIterations)
{
    return symetric ? symetric::UpperBound(Mc, Ml, e, w, betaPowerSet, d, de, p, countIterations) : UpperBound(Mc, Ml, e, w, betaPowerSet, d, de, p, countIterations);
}

int naive::symetric::UpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::set<std::vector<int>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p,
    int& countIterations)
{
    using std::begin;
    using std::end;
    using std::rbegin;
    using std::rend;
    
    auto bestM = Mc;
    #ifdef DEBUG
    std::cerr << "PPP: (";
    for(auto i: e)
        std::cerr << i << ",";
    std::cerr << ")(";
    for(auto i: w)
        std::cerr << i << ",";
    std::cerr << ")" << std::endl;
    
    std::vector<int> bestBetaSet;
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
        countIterations++;
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

int symetric::UpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<std::vector<int>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p,
    int& countIterations)
{
    using std::begin;
    using std::end;
    using std::rbegin;
    using std::rend;
    
    auto bestM = Mc;
    #ifdef DEBUG
    std::cerr << "PPP: (";
    for(auto i: e)
        std::cerr << i << ",";
    std::cerr << ")(";
    for(auto i: w)
        std::cerr << i << ",";
    std::cerr << ")" << std::endl;
    
    std::vector<int> bestBetaSet;
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

int UpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<std::vector<int>>& betaPowerSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p,
    int& countIterations)
{
    using std::begin;
    using std::end;
    using std::rbegin;
    using std::rend;
    
    auto bestM = Mc;
    #ifdef DEBUG
    std::cerr << "PPP: (";
    for(auto i: e)
        std::cerr << i << ",";
    std::cerr << ")(";
    for(auto i: w)
        std::cerr << i << ",";
    std::cerr << ")" << std::endl;
    
    std::vector<int> bestBetaSet;
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
        countIterations++;
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

Plan noDuplicate::UpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<int>& betaSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p)
{
    using std::begin;
    using std::end;
    using std::rbegin;
    using std::rend;
    
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

        i++;
        #ifdef DEBUG
        std::cerr << "    betaS: {";
        for(auto i: betaSet)
            std::cerr << i << ",";
        std::cerr << "}" << std::endl;
        #endif

        auto betaSetSize = betaSet.size();
        // Delete elements of the betaSet from w
        std::vector<Si> S(p);
        Plan plan(p);
        
        auto itE = rbegin(e);
        auto itW = rbegin(w);
        auto itP = begin(S);

        // Open the P3
        if(p >= betaSetSize) { // Avoid finding the min element that is costly
           for(unsigned i = 0; i < betaSetSize; ++i) {
                S[i].m = 2*std::max(d[betaSet[i]], de[betaSet[i]]);
                plan.cities[i].push_back(betaSet[i]);
           }
        }
        else {
            for(auto i : betaSet)
            {
                itP = min_element(begin(S), end(S), compM);
                itP->m += 2*std::max(d[i], de[i]);
                auto p = std::distance(std::begin(S), itP);
                plan.cities[p].push_back(i);
            }
        }

        // We give one P1 to every plane by plan constraint
        for(auto i = std::rbegin(w); i != std::rend(w); ++i) 
        {
            itP = min_element(begin(S), end(S), compMS);
            //std::cout << "add to " << std::distance(std::begin(S), itP) << std::endl;
            itP->m += d[*i] + de[*i];
            itP->s = WEST;
            auto p = std::distance(std::begin(S), itP);
            plan.cities[p].push_back(*i);
        }

        auto east = int{0};
        auto west = int{p};
        auto flights = int{0};
        auto ppp_s = e.size();

        while(east < ppp_s - flights)
        {
            itP = min_element(begin(S), end(S), compM);
            itP->m += d[*itE] + de[*itE];
            itP->s = !itP->s;
            auto p = std::distance(std::begin(S), itP);
            plan.cities[p].push_back(*itE);
            if(itP->s == EAST) 
            {
                east++;
                west--;
            } 
            else 
            {
                east--;
                west++;
            }
            flights++;
            itE++;
        }

        while(itE != std::rend(e))
        {
            //std::cout << " . " << std::endl;
            itP = min_element(begin(S), end(S), compMS);
            //std::cout << "add to " << std::distance(std::begin(S), itP) << std::endl;
            itP->m += d[*itE] + de[*itE];
            itP->s = !itP->s;
            auto p = std::distance(std::begin(S), itP);
            plan.cities[p].push_back(*itE);
            itE++;
        }

        // We close the P3
        for(auto i : betaSet)
        {
            itP = min_element(begin(S), end(S), compM);
            //std::cout << "add to " << std::distance(std::begin(S), itP) << std::endl;
            itP->m += 2*std::min(d[i], de[i]);
            auto p = std::distance(std::begin(S), itP);
            plan.cities[p].push_back(i);
        }

    for(unsigned i = 0; i < plan.cities.size(); ++i) {
        plan.planes_m[i] = S[i].m;
    }
    plan.m = std::max_element(begin(S),end(S), compM)->m;
    return plan;
}

/*
int noDuplicate::UpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::vector<int>& betaSet,
    const std::vector<double>& d,
    const std::vector<double>& de,
    unsigned p)
{
    using std::begin;
    using std::end;
    using std::rbegin;
    using std::rend;
    
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

        i++;
        #ifdef DEBUG
        std::cerr << "    betaS: {";
        for(auto i: betaSet)
            std::cerr << i << ",";
        std::cerr << "}" << std::endl;
        #endif

        auto betaSetSize = betaSet.size();
        // Delete elements of the betaSet from w
        std::vector<Si> S(p);
        
        auto itE = rbegin(e);
        auto itW = rbegin(w);
        auto itP = begin(S);

        // Open the P3
        if(p >= betaSetSize) { // Avoid finding the min element that is costly
           for(unsigned i = 0; i < betaSetSize; ++i) {
                S[i].m = 2*std::max(d[betaSet[i]], de[betaSet[i]]);
           }
        }
        else {
            for(auto i : betaSet)
            {
                itP = min_element(begin(S), end(S), compM);
                itP->m += 2*std::max(d[i], de[i]);
            }
        }

        // We give one P1 to every plane by plan constraint
        for(auto i = std::rbegin(w); i != std::rend(w); ++i) 
        {
            itP = min_element(begin(S), end(S), compMS);
            //std::cout << "add to " << std::distance(std::begin(S), itP) << std::endl;
            itP->m += d[*i] + de[*i];
            itP->s = WEST;
        }

        auto east = int{0};
        auto west = int{p};
        auto flights = int{0};
        auto ppp_s = e.size();

        while(east < ppp_s - flights)
        {
            itP = min_element(begin(S), end(S), compM);
            itP->m += d[*itE] + de[*itE];
            itP->s = !itP->s;
            if(itP->s == EAST) 
            {
                east++;
                west--;
            } 
            else 
            {
                east--;
                west++;
            }
            flights++;
            itE++;
        }

        while(itE != std::rend(e))
        {
            //std::cout << " . " << std::endl;
            itP = min_element(begin(S), end(S), compMS);
            //std::cout << "add to " << std::distance(std::begin(S), itP) << std::endl;
            itP->m += d[*itE] + de[*itE];
            itP->s = !itP->s;
            itE++;
        }

        // We close the P3
        for(auto i : betaSet)
        {
            itP = min_element(begin(S), end(S), compM);
            //std::cout << "add to " << std::distance(std::begin(S), itP) << std::endl;
            itP->m += 2*std::min(d[i], de[i]);
        }

    return std::max_element(begin(S),end(S), compM)->m;
}
*/