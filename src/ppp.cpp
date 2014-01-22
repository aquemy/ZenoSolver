#include <fstream>
#include <algorithm>
#include <vector>
#include <ppp.hpp>

#include <iostream> // Debug only

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

std::vector<PPP> cartesianProduct(
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W,
    const std::vector<double>& c,
    const std::vector<double>& d,
    unsigned p)
{
    std::vector<PPP> PPPSet;
    PPPSet.reserve(E.size()*W.size());
    unsigned ie = 0;
    unsigned iw = 0;
    long unsigned count = 0;
    for(auto& e : E)
    {
        iw = 0;
        double CostEast = 0;
        std::for_each(std::begin(e),std::end(e),[&](unsigned i) { CostEast += c[i];});
        double MlEast = 0;
        std::for_each(std::begin(e),std::end(e),[&](unsigned i) { MlEast += 2*d[i];});
        for(auto& w : W)
        {
            double Cost = CostEast;
            std::for_each(std::begin(w),std::end(w),[&](unsigned i) { Cost += c[i];});
            double Ml = MlEast;
            std::for_each(std::begin(w),std::end(w),[&](unsigned i) { Ml += 2*d[i];});
            // Note : We compute BetaMax only after the computation of the GreedyUpperBound with Beta = 0
            //        In this case it is possible to avoid such a computation for already pruned PPP.
            PPPSet.push_back(PPP(ie, iw, Cost, Ml / p, Ml));
            iw++;
            std::cerr << count << " " << std::endl;
            count++;
            
        }
        ie++;
    }
    return std::move(PPPSet);
}

