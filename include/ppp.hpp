#ifndef _ZS_PPP_
#define _ZS_PPP_

struct PPP
{
    PPP(unsigned _e, unsigned _w, double _C, double _Ms, double _Mc);
   
    void computeBetaMax(const std::vector<std::vector<int>>& E, const std::vector<std::vector<int>>& W);
   
    bool operator==(const PPP& o) const;
    
    bool operator!=(const PPP& o) const;

    // Cities : for better memory usage, we only store the indexes in E and W tupple sets.
    unsigned e;
    unsigned w;
    // Cost
    double C;
    // Makespan
    double Ms; // Theoretical minimum makespan
    double Mc; // Current makespan (initialized with Ml)
    // Pattern 3
    unsigned betaMax = 0;
    std::vector<int> betaSet;

};

bool SortByCost(PPP i, PPP j);
bool SortByMakespan(PPP i, PPP j);

std::vector<PPP> cartesianProduct(
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W,
    const std::vector<double>& c,
    const std::vector<double>& d,
    unsigned p);

#endif // _ZS_PPP_
