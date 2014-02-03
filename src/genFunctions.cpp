#include <vector>
#include <functional>
#include <cmath>
#include <genFunctions.hpp>

void apply(std::vector<double>& v, std::function<double(unsigned)> f, double x, double y, double scale, double trans)
{
    for(unsigned i = 0; i < v.size(); i++)
        v[i] = x*f(scale*(i+1)+trans) + y;
}

void rapply(std::vector<double>& v, std::function<double(unsigned)> f, double x, double y, double scale, double trans)
{
    for(unsigned i = 0; i < v.size(); i++)
        v[i] = x*f(scale*(v.size()-i)+trans)+y;
}

double f1(unsigned i) { return std::log(i); }
double f2(unsigned i) { return std::sqrt(i); }
double f3(unsigned i) { return i; }
double f4(unsigned i) { return pow(2,i); }
double f5(unsigned i) { return 5*(i / 3) + 0.1*(i % 3); }

