#include <vector>
#include <functional>
#include <cmath>
#include <genFunctions.hpp>

void apply(std::vector<double>& v, std::function<double(unsigned)> f)
{
    for(unsigned i = 0; i < v.size(); i++)
        v[i] = f(v[i]);
}

double f1(unsigned i) { return std::log(i); }
double f2(unsigned i) { return std::sqrt(i); }
double f3(unsigned i) { return i; }
double f4(unsigned i) { return pow(2,i); }
double f5(unsigned i) { return 2*i; }
