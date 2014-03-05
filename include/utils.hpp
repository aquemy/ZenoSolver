#ifndef _ZS_UTILS_
#define _ZS_UTILS_
 
#include <functional>
#include <map>

class PPP;

void debugPrint(std::string title, std::function<void(void)> f);

void dump(const std::vector<PPP>& set, 
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W);

void dumpPPP(const PPP& ppp, 
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W);

bool isReadable(const std::string& path);

void generatePDDL(std::string path, unsigned n, unsigned t, unsigned p, 
    const std::vector<double>& c, 
    const std::vector<double>& d, 
    const std::map<int,int>& pareto = std::map<int,int>());

#endif // _ZS_UTILS_


