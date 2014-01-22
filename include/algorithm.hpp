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

double UpperBound(const PPP& ppp,
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W,
    const std::vector<double>& d, 
    unsigned p, 
    unsigned beta);
    
bool isGreedilyDominated(const PPP& ppp, const std::vector<PPP>&);

#endif // _ZS_ALGORITHM_
