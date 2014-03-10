#ifndef _ZS_UTILS_
#define _ZS_UTILS_
 
#include <functional>
#include <map>

void debugPrint(std::string title, std::function<void(void)> f);

bool isReadable(const std::string& path);

void generatePDDL(std::string path, unsigned n, unsigned t, unsigned p, 
    const std::vector<double>& c, 
    const std::vector<double>& d, 
    const std::map<int,int>& pareto = std::map<int,int>());

#endif // _ZS_UTILS_


