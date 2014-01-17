#ifndef _ZS_ALGORITHM_
#define _ZS_ALGORITHM_

struct PPP;

double SimpleUpperBound(const PPP& ppp, 
    const std::vector<std::vector<int>>& E,
    const std::vector<double>& d, 
    unsigned p, 
    unsigned t);

double UpperBound(const PPP& ppp,
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W,
    const std::vector<double>& d, 
    unsigned p, 
    unsigned beta);
    
bool isGreedyDominated(const PPP& ppp, const std::vector<PPP>&);

#endif // _ZS_ALGORITHM_
