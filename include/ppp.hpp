#ifndef _ZS_PPP_
#define _ZS_PPP_

struct PPP
{
    PPP(std::vector<int>& _e, std::vector<int>& _w, double _C, double _Ms, double _Mc);
   
    void computeBetaMax();
   
    bool operator==(const PPP& o);
    
    friend std::ostream& operator <<(std::ostream& _os, const PPP& _ppp);

// Cities
std::vector<int> e;
std::vector<int> w;
// Cost
double C;
// Makespan
double Ms; // Theoretical minimum makespan
double Mc; // Current makespan (should be initialized with Ml ?)
// Pattern 3
unsigned betaMax = 0;
std::vector<int> betaSet;

// Dominated
bool dominated = false; // Flag to prune during the computation regarding greedy domination

#ifdef STATS
unsigned nbEval = 0;
#endif // STATS

};

bool SortByCost(PPP i, PPP j);
bool SortByMakespan(PPP i, PPP j);


#endif // _ZS_PPP_
