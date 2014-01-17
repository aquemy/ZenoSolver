#ifndef _ZS_UTILS_
#define _ZS_UTILS_

class PPP;

void debugPrint(std::string _title, std::function<void(void)> _f);

void dump(const std::vector<PPP>& _set);

bool isReadable(const std::string & _path);

#endif // _ZS_UTILS_


