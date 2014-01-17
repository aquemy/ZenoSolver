#include <algorithm>
#include <vector>
#include <algorithm.hpp>
#include <ppp.hpp>

double SimpleUpperBound(const PPP& ppp, const std::vector<double>& d, unsigned p, unsigned t)
{
    std::vector<double> M(p);

    for(unsigned i = 0; i < p; i++)
    {
        M[i] += 2*d[ppp.e[i]];
    }
    
    for(unsigned i = 0; i < t-p; i++)
    {
        unsigned minPlane = distance(begin(M), min_element(begin(M), end(M)));
        M[minPlane] += 2*d[ppp.e[p+i]] + 2*d[ppp.w[i]];
    }
      
    return *max_element(begin(M),end(M));
}

double UpperBound(const PPP& ppp, const std::vector<double>& d, unsigned p, unsigned beta)
{
    std::vector<double> M(p);   
            
    auto betaSet = ppp.betaSet;
    betaSet.resize(beta);
            
    decltype(ppp.e) alphaWSet;
    set_difference (begin(ppp.w), end(ppp.w), begin(betaSet), end(betaSet), back_inserter(alphaWSet));
            
    decltype(ppp.e) alphaESet;
    decltype(ppp.e) diff;
    set_intersection (begin(ppp.e), end(ppp.e), begin(betaSet), end(betaSet), back_inserter(diff));
    set_difference (begin(ppp.e), end(ppp.e), begin(diff), end(diff), back_inserter(alphaESet));
                
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
        nth_element(begin(M), begin(M)+1, end(M)); // Place only the element we need in order to avoid complete sorting

        M[minPlane] += 2*d[betaSet[i]];
        M[1] += 2*d[betaSet[i]];
    }
            
    return *max_element(begin(M),end(M)); 
}
