#include <algorithm>
#include <vector>
#include <algorithm.hpp>
#include <ppp.hpp>

double SimpleUpperBound(const PPP& ppp, 
    const std::vector<std::vector<int>>& E,
    const std::vector<double>& d, 
    unsigned p, 
    unsigned t)
{
    std::vector<double> M(p);

    for(unsigned i = 0; i < p; i++)
    {
        M[i] += 2*d[E[ppp.e][i]];
    }
    
    for(unsigned i = 0; i < t-p; i++)
    {
        unsigned minPlane = distance(begin(M), min_element(begin(M), end(M)));
        M[minPlane] += 2*d[E[ppp.e][p+i]] + 2*d[E[ppp.w][i]];
    }
      
    return *max_element(begin(M),end(M));
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

    std::vector<double> M(p);
    auto e = E[ppp.e];
    auto w = W[ppp.w]; 
            
    auto betaSet = ppp.betaSet;
    betaSet.resize(beta);
            
    decltype(e) alphaWSet;
    std::set_difference (begin(w), end(w), begin(betaSet), end(betaSet), std::back_inserter(alphaWSet));
            
    decltype(e) alphaESet;
    decltype(e) diff;
    std::set_intersection (begin(e), end(e), begin(betaSet), end(betaSet), std::back_inserter(diff));
    std::set_difference (begin(e), end(e), begin(diff), end(diff), std::back_inserter(alphaESet));
                
    // Pattern 1
    unsigned card = p;
    for(unsigned i = 0; i < card; i++)
        M[i] += 2*d[alphaESet[i]];
    
    // Pattern 2        
    card = alphaWSet.size();
    for(unsigned i = 0; i < card; i++)
    {
        unsigned minPlane = distance(begin(M), min_element(begin(M), end(M)));
        M[minPlane] += 2*d[alphaWSet[i]] + 2*d[alphaESet[p+i]];
    }
            
    // Pattern 3
    for(unsigned i = 0; i < beta; i++)
    {
        unsigned minPlane = distance(begin(M), min_element(begin(M), end(M)));
        std::nth_element(begin(M), begin(M)+1, end(M)); // Place only the element we need in order to avoid complete sorting

        M[minPlane] += 2*d[betaSet[i]];
        M[1] += 2*d[betaSet[i]];
    }
            
    return *std::max_element(begin(M),end(M)); 
}

bool isGreedilyDominated(const PPP& ppp, const std::vector<PPP>& PPPSet)
{
    for(const auto& j : PPPSet)
        if((j != ppp) && ((j.C <= ppp.C) && (j.Mc < ppp.Ms))) 
            return true;

    return false;
}

