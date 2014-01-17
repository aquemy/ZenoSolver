#include <fstream>
#include <algorithm>
#include <vector>
#include <ppp.hpp>

PPP::PPP(unsigned _e, unsigned _w, double _C, double _Ms, double _Mc) :
    e(_e),
    w(_w),
    C(_C),
    Ms(_Ms),
    Mc(_Mc)
    {}
   
void PPP::computeBetaMax(const std::vector<std::vector<int>>& E, const std::vector<std::vector<int>>& W)
{
    auto e = E[this->e];
    auto w = W[this->w];

    betaSet.clear();

    decltype(w) diff;
    set_difference (begin(w), end(w), begin(e), end(e), back_inserter(diff));
    set_difference (begin(w), end(w), begin(diff), end(diff), back_inserter(betaSet));

    betaMax = betaSet.size();
}
   
bool PPP::operator==(const PPP& o) const
{
    return (this->C == o.C) and (this->Mc == o.Mc);
}    

bool PPP::operator!=(const PPP& o) const
{
    return !(*this == o);
}    


bool SortByCost(PPP i, PPP j) { return i.C < j.C; }
bool SortByMakespan(PPP i, PPP j) { return i.Mc < j.Mc; }

