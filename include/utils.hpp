#ifndef _ZS_UTILS_
#define _ZS_UTILS_

class PPP;

void debugPrint(std::string title, std::function<void(void)> f);

void dump(const std::vector<PPP>& set, 
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W);

void dumpPPP(const PPP& ppp, 
    const std::vector<std::vector<int>>& E, 
    const std::vector<std::vector<int>>& W);

bool isReadable(const std::string& path);

#endif // _ZS_UTILS_


