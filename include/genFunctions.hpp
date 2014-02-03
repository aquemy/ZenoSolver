#ifndef _ZS_GEN_FUNCTION_
#define _ZS_GEN_FUNCTION_

void apply(std::vector<double>& v, std::function<double(unsigned)> f, double x = 1, double y = 0, double scale = 1, double trans = 0);
void rapply(std::vector<double>& v, std::function<double(unsigned)> f, double x = 1, double y = 0, double scale = 1, double trans = 0);

double f1(unsigned i);
double f2(unsigned i);
double f3(unsigned i);
double f4(unsigned i);
double f5(unsigned i);
double f6(unsigned i);

#endif // _ZS_GEN_FUNCTION_
