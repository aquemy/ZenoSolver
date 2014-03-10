#ifndef _ZS_ALGORITHM_
#define _ZS_ALGORITHM_

struct PPP;

struct Si
{
    double m = 0;
    bool s = true; // Next Eastbound flight = true
};

//bool compM(Si& i, Si& j);
bool compM(const Si i, const Si j);
bool compMS(Si& i, Si& j);

double SimpleUpperBound(const PPP& ppp, 
    const std::vector<std::vector<int>>& E,
    const std::vector<std::vector<int>>& W,
    const std::vector<double>& d, 
    unsigned p);

int UpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::set<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    unsigned p);
    
bool isGreedilyDominated(const PPP& ppp, const std::vector<PPP>&);

#endif // _ZS_ALGORITHM_
