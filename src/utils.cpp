#include <iostream>
#include <fstream>
#include <iomanip>
#include <vector>
#include <functional>
#include <utils.hpp>
#include <ppp.hpp>

void debugPrint(std::string title, std::function<void(void)> f)
{
    std::cerr << std::setfill('=') << std::setw(42) << "=" << std::endl;
    std::cerr << "==" << std::setfill(' ') << std::setw((38 - title.size()) / 2 + 1) << " ";
    std::cerr << title;
    std::cerr << std::setfill(' ') << std::setw((38 - title.size()) / 2 + 1) << "==" << std::endl;
    std::cerr << std::setfill('=') << std::setw(42) << "=" << std::endl;
    f();
}

void dump(const std::vector<PPP>& set, 
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W)
{
    for(auto& ppp : set)
        dumpPPP(ppp, E, W);
}

void dumpPPP(const PPP& ppp, 
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W)
{
    std::cerr << "PPP = (";
    for(auto i : E[ppp.e])
        std::cerr << i << ",";
    std::cerr << ")(";
    for(auto i : W[ppp.w])
        std::cerr << i << ",";
    std::cerr << ")" << std::endl;
    std::cerr << " - Cost          : " << ppp.C << std::endl;
    std::cerr << " - Min. Makespan : " << ppp.Ms << std::endl;
    std::cerr << " - Cur. Makespan : " << ppp.Mc << std::endl;
    std::cerr << " - Beta Max      : " << ppp.betaMax << std::endl;
}

bool isReadable(const std::string& path) 
{ 
    std::ifstream file(path.c_str()); 
    return !file.fail(); 
}

