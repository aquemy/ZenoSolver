#include <fstream>
#include <algorithm>
#include <vector>
#include <ppp.hpp>

PPP::PPP(std::vector<int>& _e, std::vector<int>& _w, double _C, double _Ms, double _Mc) :
    e(_e),
    w(_w),
    C(_C),
    Ms(_Ms),
    Mc(_Mc)
    {}
   
void PPP::computeBetaMax()
{
    betaSet.clear();

    decltype(w) diff;
    set_difference (begin(w), end(w), begin(e), end(e), back_inserter(diff));
    set_difference (begin(w), end(w), begin(diff), end(diff), back_inserter(betaSet));

    betaMax = betaSet.size();
}
   
bool PPP::operator==(const PPP& o)
{
    return (this->C == o.C) and (this->Mc == o.Mc);
}    

std::ostream& operator <<(std::ostream& _os, const PPP& _ppp)
{
    _os << "PPP = (";
    for(auto i : _ppp.e)
        _os << i << ",";
    _os << ")(";
    for(auto i : _ppp.w)
        _os << i << ",";
    _os << ")" << std::endl;
    _os << " - Cost          : " << _ppp.C << std::endl;
    _os << " - Min. Makespan : " << _ppp.Ms << std::endl;
    _os << " - Cur. Makespan : " << _ppp.Mc << std::endl;
    _os << " - Beta Max      : " << _ppp.betaMax << std::endl;
    
    return _os;
}

bool SortByCost(PPP i, PPP j) { return i.C < j.C; }
bool SortByMakespan(PPP i, PPP j) { return i.Mc < j.Mc; }
