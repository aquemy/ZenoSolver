#ifndef _ZS_ALGORITHM_
#define _ZS_ALGORITHM_

struct PPP;

double SimpleUpperBound(const PPP& ppp, const std::vector<double>& d, unsigned p, unsigned t);

double UpperBound(const PPP& ppp, const std::vector<double>& d, unsigned p, unsigned beta);

#endif // _ZS_ALGORITHM_
