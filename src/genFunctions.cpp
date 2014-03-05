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
double f5(unsigned i) { return 5*(i / 2) + 0.1*(i % 2); }

/*
[aquemy@rlm build]$ ./zenoSolver -n 3 -t 6 -p 2 -j 2.9 -aP > t
c : 2000 1010 500 
d : 500 1010 2000 

[aquemy@rlm build]$ ./zenoSolver -n 3 -t 3 -p 2 -j 3.9 -aP > t
c : 2510 1510 509 
d : 509 1510 2510

c : 2000 1510 1500 1010 
d : 1010 1500 1510 2000

*/
