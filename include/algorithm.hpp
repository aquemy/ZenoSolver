#ifndef _ZS_ALGORITHM_
#define _ZS_ALGORITHM_

struct Si
{
    double m = 0;
    bool s = true; // Next Eastbound flight = true
};

//bool compM(Si& i, Si& j);
bool compM(const Si i, const Si j);
bool compMS(Si& i, Si& j);

int UpperBound(int Mc, 
    int Ml, 
    const std::vector<int>& e, 
    const std::vector<int>& w,
    const std::set<std::vector<unsigned>>& betaPowerSet,
    const std::vector<double>& d,
    unsigned p);

#endif // _ZS_ALGORITHM_
